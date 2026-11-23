/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpPermHealProg
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Frame Primitives, Lookup, and Overmars Rebuild `Memory.Prog` Subroutines

This module implements the foundational parameter-free `Memory.Prog` subroutines and
`Realizes .exact` certificates for `FastMemRep` in `SuccinctWhpModel`:

1. Compositional `FastStateStep` transition frame lemmas and atomic field accessors on `FastMemRep`
   (headers, `bktMeta` scalars, `locState`, `quotArr`, `valArr`, `backPtr`, `poolFreeStack`,
   `poolOwner`, `dirtyBuckets`, `physSlot`, `rKeyAt`, `fpAt`, `inLiveTree`, and `matchesKey`).
2. `fastFindLocBqGenProg` and `fastQueryGenProg`: worst-case `O_c(1)` coordinate and value lookup
   across `buf curEp`, `buf oldEp`, and `liveSlice[b]`.
3. `overmarsScanLoopGenProg` and `overmarsStepGenProg`: worst-case `O_c(1)` per-bucket Overmars
   shadow B+-tree scan (`16` coordinates via `Realizes.iterate₀`) and role swap.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.FastStateStep`: compositional invariant
  preserving `SeedWhpMemRep`, `FastMemRep`, `frontier`, and memory outside `largeSpaceWhp`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastQueryGenProg`,
  `overmarsStepGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastQueryGen`,
  `fastQueryGenProg_spec`, `realizes_overmarsStepGen`, `overmarsStepGenProg_fastStep`.
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

/-! ## Section 1: Primitive `Memory.Prog` Lemmas and Segment Bounds -/

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Auxiliary index bounds in the large regime (`whpThreshold c ≤ n_max`). -/
theorem large_index_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    numBucketsWhp n_max * capBackWhp n_max ≤ n_max ∧
    numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max = n_max ∧
    2 * totalLocalCoordsWhp n_max + 32 ≤ n_max ∧
    poolSizeWhp n_max ≤ n_max ∧
    3 * numBucketsWhp n_max ≤ n_max ∧
    6 * qEpochWhp n_max + 6 ≤ n_max := by
  have hL2 := two_le_slabScale n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  obtain ⟨hM_ge, _, _, _, _, _, _, _⟩ := large_bounds_lt_n_max hth
  obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
  have hg_pos := globalPtrBits_pos_of_large hth
  have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
  have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
    unfold capBackWhp
    calc 2 * (slabScale n_max) ^ 11 ≤ slabScale n_max * (slabScale n_max) ^ 11 :=
          Nat.mul_le_mul_right _ hL2
      _ = (slabScale n_max) ^ 12 := by ring
  have hmcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have hmcf : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max := by
    calc numBucketsWhp n_max * capFrontWhp n_max
        ≤ numBucketsWhp n_max * (n_max / numBucketsWhp n_max) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ n_max := Nat.mul_div_le _ _
  have hps_eq : numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max = n_max := by
    unfold poolSizeWhp; omega
  have h2tl : 2 * totalLocalCoordsWhp n_max + 32 ≤ n_max := by
    have htl3 : totalLocalCoordsWhp n_max ≤ 3 * (slabScale n_max) ^ 12 :=
      totalLocalCoordsWhp_le_three_mul
    have h1024L12 : 1024 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ hM_ge).trans hML12
    have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (by omega)
    omega
  exact ⟨hmcb, hps_eq, h2tl, by omega, by omega, h6q⟩

private theorem packed_safe_true {c U V w n_max base off N k idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hk : k ≤ w) (hidx : idx < N)
    (hseg : off + packedWords N k w ≤ largeSpaceWhp c U V w n_max) :
    ∃ N', True ∧ 0 < w ∧ k ≤ w ∧ idx < N' ∧ Fits w (base + off + packedWords N' k w) := by
  obtain ⟨N', _, h2, h3, h4, h5⟩ := henv.packed_safe_of_le hk hidx hseg
  exact ⟨N', trivial, h2, h3, h4, h5⟩

private theorem mul_add_inj_right {B a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ < B) (hb₂ : b₂ < B)
    (heq : a₁ * B + b₁ = a₂ * B + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hB : 0 < B := by omega
  have ha : a₁ = a₂ := by
    have hd1 : (a₁ * B + b₁) / B = a₁ := by
      rw [Nat.mul_comm a₁ B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb₁, Nat.add_zero]
    have hd2 : (a₂ * B + b₂) / B = a₂ := by
      rw [Nat.mul_comm a₂ B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb₂, Nat.add_zero]
    rw [← hd1, heq, hd2]
  exact ⟨ha, by subst ha; omega⟩

/-! ## Section 2: `FastStateStep` and Compositional `FastMemRep` Frame Lemmas -/

/-- Bundled transition invariant for fast-mode `Memory.Prog` substeps: preserves `frontier`,
`SeedWhpMemRep`, `FastMemRep` for `fs'`, and all memory words outside
`[base, base + largeSpaceWhp c U V w n_max)`. -/
@[expose] def FastStateStep (base c U V w n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs' : FastState) (s s' : Memory.State) : Prop :=
  s'.frontier = s.frontier ∧
  SeedWhpMemRep base c U w n_max θ s'.mem ∧
  FastMemRep base c U V w n_max fs' s'.mem ∧
  (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a)

theorem FastStateStep.refl {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    FastStateStep base c U V w n_max θ fs s s :=
  ⟨rfl, hseed, hrep, fun _ _ => rfl⟩

theorem FastStateStep.trans {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs₁ fs₂ : FastState} {s₀ s₁ s₂ : Memory.State}
    (h₁ : FastStateStep base c U V w n_max θ fs₁ s₀ s₁)
    (h₂ : FastStateStep base c U V w n_max θ fs₂ s₁ s₂) :
    FastStateStep base c U V w n_max θ fs₂ s₀ s₂ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1, h₂.2.2.1, fun a ha => (h₂.2.2.2 a ha).trans (h₁.2.2.2 a ha)⟩

/-- `BTreeSliceMemRep` invariance when `offBktMeta` (`[10..15]`) and `[offBtMeta, offTrieChild0)`
are unchanged. -/
theorem bTreeSliceMemRep_congr {base c U V w n_max sIdx : ℕ} {sl : BTreeSlice}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hbm : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂
        (16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)) =
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁
        (16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)) ∧
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂
        (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) =
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁
        (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)))
    (hbt : ∀ a, base + offBtMeta c U V w n_max ≤ a → a < base + offTrieChild0 c U V w n_max →
      mem₂ a = mem₁ a)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl mem₁) :
    BTreeSliceMemRep base c U V w n_max sIdx sl mem₂ := by
  have hch := largeOffsetChain c U V w n_max
  obtain ⟨ha_le, ha_r, hr_r, hnd⟩ := hrep
  refine ⟨ha_le, hbm.1.trans ha_r, hbm.2.trans hr_r, fun u hu => ?_⟩
  have hidx : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
    unfold totalBTreeNodesWhp
    exact mul_add_lt_mul_bound hsIdx (hu.trans_le ha_le)
  exact ⟨(readPacked_congr hw (hidx := hidx) fun a ⟨h1,
    h2⟩ => hbt a h1 (by omega)).trans (hnd u hu).1,
    (readPacked_congr hw (hidx := hidx) fun a ⟨h1,
      h2⟩ => hbt a (by omega) (by omega)).trans (hnd u hu).2.1,
    (readPacked_congr hw (hidx := hidx) fun a ⟨h1,
      h2⟩ => hbt a (by omega) (by omega)).trans (hnd u hu).2.2⟩

/-- `BufTrieMemRep` invariance when headers `12..15` and `[offTrieChild0, largeSpaceWhp)` are
unchanged (or `offTrieItems0` is only modified at indices `≥ 3 * qEpochWhp`). -/
private theorem bufTrieMemRep_congr_nonBuf {base c U V w n_max ep : ℕ} {tr : BufTrie}
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
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hchild, hpar, hleaf, hitems⟩ := hrep
  rcases hep with rfl | rfl
  · simp only [↓reduceIte] at hhdr_na hhdr_ia hchild hpar hleaf hitems ⊢
    refine ⟨hna, hia,
      (hhdr 12 (by decide) (by decide)).trans hhdr_na,
      (hhdr 13 (by decide) (by decide)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hi : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max :=
        mul_add_lt_mul_bound hu hch_lt
      exact (readPacked_congr hw (hidx := hi) fun a ⟨h1, h2⟩ => htrie a h1 (by omega)).trans
        (hchild u hu ch hch_lt)
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hpar u hu1 hu).1,
        (readPacked_congr hw (hidx := show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hleaf u hu).1,
        fun hnz =>
          (readPacked_congr hw (hidx := show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans ((hleaf u hu).2 hnz)⟩
    · have hid_q : id < qEpochWhp n_max := hid.trans_le hia
      exact ⟨(hit0 id (by omega)).trans (hitems id hid).1,
        (hit0 _ (by omega)).trans (hitems id hid).2.1,
        (hit0 _ (by omega)).trans (hitems id hid).2.2⟩
  · simp only [Nat.one_ne_zero, ↓reduceIte] at hhdr_na hhdr_ia hchild hpar hleaf hitems ⊢
    refine ⟨hna, hia,
      (hhdr 14 (by decide) (by decide)).trans hhdr_na,
      (hhdr 15 (by decide) (by decide)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hi : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max :=
        mul_add_lt_mul_bound hu hch_lt
      exact (readPacked_congr hw (hidx := hi) fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans
        (hchild u hu ch hch_lt)
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hpar u hu1 hu).1,
        (readPacked_congr hw (hidx := show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hpar u hu1 hu).2⟩
    · exact ⟨(readPacked_congr hw (hidx := show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans (hleaf u hu).1,
        fun hnz =>
          (readPacked_congr hw (hidx := show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega)
          fun a ⟨h1, h2⟩ => htrie a (by omega) (by omega)).trans ((hleaf u hu).2 hnz)⟩
    · have hid_q : id < qEpochWhp n_max := hid.trans_le hia
      exact ⟨(readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
          fun a ⟨h1, h2⟩ => hit1 a h1 (by omega)).trans (hitems id hid).1,
        (readPacked_congr hw (hidx := show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          fun a ⟨h1, h2⟩ => hit1 a h1 (by omega)).trans (hitems id hid).2.1,
        (readPacked_congr hw (hidx :=
          show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega)
          fun a ⟨h1, h2⟩ => hit1 a h1 (by omega)).trans (hitems id hid).2.2⟩

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
    fun b hb => ?_,
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
  · have hm := hbmeta b hb
    have h9 : ∀ k < 10,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + k) =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
            (16 * b + k) :=
      fun k hk => hrp_pre (show 16 * b + k < 16 * numBucketsWhp n_max by omega)
        (by omega) (by omega)
    exact ⟨(h9 0 (by decide)).trans hm.1,
      (h9 1 (by decide)).trans hm.2.1,
      (h9 2 (by decide)).trans hm.2.2.1,
      (h9 3 (by decide)).trans hm.2.2.2.1,
      (h9 4 (by decide)).trans hm.2.2.2.2.1,
      (h9 5 (by decide)).trans hm.2.2.2.2.2.1,
      (h9 6 (by decide)).trans hm.2.2.2.2.2.2.1,
      (h9 7 (by decide)).trans hm.2.2.2.2.2.2.2.1,
      (h9 8 (by decide)).trans hm.2.2.2.2.2.2.2.2.1,
      (h9 9 (by decide)).trans hm.2.2.2.2.2.2.2.2.2⟩
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
    fun b hb => ?_,
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
  · have hm := hbmeta b hb
    have h9 : ∀ k < 10,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + k) =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
            (16 * b + k) :=
      fun k hk => hbm (16 * b + k) (by omega) (by omega) (by omega)
    exact ⟨(h9 0 (by decide)).trans hm.1,
      (h9 1 (by decide)).trans hm.2.1,
      (h9 2 (by decide)).trans hm.2.2.1,
      (h9 3 (by decide)).trans hm.2.2.2.1,
      (h9 4 (by decide)).trans hm.2.2.2.2.1,
      (h9 5 (by decide)).trans hm.2.2.2.2.2.1,
      (h9 6 (by decide)).trans hm.2.2.2.2.2.2.1,
      (h9 7 (by decide)).trans hm.2.2.2.2.2.2.2.1,
      (h9 8 (by decide)).trans hm.2.2.2.2.2.2.2.2.1,
      (h9 9 (by decide)).trans hm.2.2.2.2.2.2.2.2.2⟩
  · by_cases heq : sIdx' = sIdx
    · subst heq; simpa only [Function.update_self] using hsl'
    · simpa only [Function.update_of_ne heq] using hoth sIdx' hsIdx' heq _ (hslices sIdx' hsIdx')

/-- Master frame helper for scalar/array updates that leave `slices` and `buf` unchanged. -/
private theorem fastStep_nonSliceNonBuf {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
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
  rcases hhdrs with ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩
  refine ⟨hfr, hseed', ⟨hdc_le, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11,
    hqv, hloc, hbmeta, hbptr, hpool, fun sIdx hsIdx => ?_, ?_, ?_, hdirty⟩, hout⟩
  · rw [hsl_eq]
    have hrole_lt : sIdx % 3 < 3 := Nat.mod_lt _ (by decide)
    exact bTreeSliceMemRep_congr hw hsIdx
      ⟨hbm_sl _ (by omega) (by omega), hbm_sl _ (by omega) (by omega)⟩
      (fun a ha1 ha2 => hfence a (Or.inr (Or.inr (Or.inl ⟨ha1, by omega⟩))))
      (hslices0 sIdx hsIdx)
  · rw [hbuf_eq]
    exact bufTrieMemRep_congr_nonBuf hw (Or.inl rfl)
      (fun h h12 h16 => hfence (base + h) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      (fun a ha1 ha2 => hfence a (Or.inr (Or.inr (Or.inl ⟨by omega, ha2⟩))))
      hit0 (fun a ha1 _ => hfence a (Or.inr (Or.inr (Or.inr ha1)))) hbuf0
  · rw [hbuf_eq]
    exact bufTrieMemRep_congr_nonBuf hw (Or.inr rfl)
      (fun h h12 h16 => hfence (base + h) (Or.inr (Or.inl ⟨by omega, by omega⟩)))
      (fun a ha1 ha2 => hfence a (Or.inr (Or.inr (Or.inl ⟨by omega, ha2⟩))))
      hit0 (fun a ha1 _ => hfence a (Or.inr (Or.inr (Or.inr ha1)))) hbuf1

/-! ### B+-Tree Slice `FastStateStep` Wrappers -/

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
  have hch := largeOffsetChain c U V w n_max
  have hsl_rep := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx
  obtain ⟨hfr, hmc, hvp, hsl', hoth, hout⟩ :=
    btreeDeleteGenProg_spec henv hsIdx hins hsl_rep hv hq (s := s)
  refine ⟨hmc, hvp, fastStep_of_sliceUpdate henv.2.1 hsIdx hfr hseed hrep hsl' hoth ?_ ?_⟩
  · intro idx hidx _ _
    exact readPacked_congr henv.2.1 (hidx := hidx) fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega))
  · intro a ha
    rcases ha with h1 | ⟨_, h2⟩ | h3
    · exact hout a (Or.inl (by omega))
    · exact hout a (Or.inl h2)
    · exact hout a (Or.inr h3)

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
  have hch := largeOffsetChain c U V w n_max
  have hsl_rep := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx
  obtain ⟨hfr, hmc, hvp, hsl', hoth, hout⟩ :=
    btreeUpdateGenProg_spec henv hsIdx hins hsl_rep hv hq hval (s := s)
  refine ⟨hmc, hvp, fastStep_of_sliceUpdate henv.2.1 hsIdx hfr hseed hrep hsl' hoth ?_ ?_⟩
  · intro idx hidx _ _
    exact readPacked_congr henv.2.1 (hidx := hidx) fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega))
  · intro a ha
    rcases ha with h1 | ⟨_, h2⟩ | h3
    · exact hout a (Or.inl (by omega))
    · exact hout a (Or.inl h2)
    · exact hout a (Or.inr h3)

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

/-! ### `FastMemRep` Projections and `BufTrie` `FastStateStep` Wrappers -/

theorem FastMemRep.slice_rep {base c U V w n_max sIdx : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs mem) :
    BTreeSliceMemRep base c U V w n_max sIdx (fs.slices sIdx) mem :=
  hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 sIdx hsIdx

theorem FastMemRep.buf_rep {base c U V w n_max ep : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs mem) :
    BufTrieMemRep base c U V w n_max ep (fs.buf ep) mem := by
  rcases hep with rfl | rfl
  · exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bufTrie_caps_of_bounds {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) {tr : BufTrie}
    (hia : tr.itemAlloc ≤ 2 * sMaxWhp c n_max)
    (hna : tr.nodeAlloc ≤ 1 + cTabWhp c * tr.itemAlloc) :
    tr.nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
    tr.itemAlloc < qEpochWhp n_max := by
  have hlt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hia_lt : tr.itemAlloc < qEpochWhp n_max := hia.trans_lt hlt
  refine ⟨?_, hia_lt⟩
  unfold maxTrieNodesWhp
  calc tr.nodeAlloc + cTabWhp c
      ≤ 1 + cTabWhp c * tr.itemAlloc + cTabWhp c := Nat.add_le_add_right hna _
    _ = 1 + cTabWhp c * (tr.itemAlloc + 1) := by ring
    _ ≤ 1 + cTabWhp c * qEpochWhp n_max := Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_lt) 1
    _ ≤ (cTabWhp c + 1) * qEpochWhp n_max + 2 := by nlinarith

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

/-! ## Section 3: Atomic Scalar and Packed-Array Subroutines on `FastMemRep` -/

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
        have hm := hbmeta0 b hb
        have h9 : ∀ k < 10,
            readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w m' (16 * b + k) =
              readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
                (16 * b + k) :=
          fun k hk => hrp32 (show 16 * b + k < 16 * numBucketsWhp n_max by omega) (by omega)
        exact ⟨(h9 0 (by decide)).trans hm.1,
          (h9 1 (by decide)).trans hm.2.1,
          (h9 2 (by decide)).trans hm.2.2.1,
          (h9 3 (by decide)).trans hm.2.2.2.1,
          (h9 4 (by decide)).trans hm.2.2.2.2.1,
          (h9 5 (by decide)).trans hm.2.2.2.2.2.1,
          (h9 6 (by decide)).trans hm.2.2.2.2.2.2.1,
          (h9 7 (by decide)).trans hm.2.2.2.2.2.2.2.1,
          (h9 8 (by decide)).trans hm.2.2.2.2.2.2.2.2.1,
          (h9 9 (by decide)).trans hm.2.2.2.2.2.2.2.2.2⟩)
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

/-- Read bucket `b`'s scalar metadata field `field < 10` (`d = (((cp, base), b), field)`). -/
@[irreducible] def readBktFieldGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
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
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hfield⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hb ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
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
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hbm_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
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
@[irreducible] def writeBktFieldGenProg :
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
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hfield⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hb ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
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
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hbm_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
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
        exact ⟨(readPacked_congr hw (hidx := hi) fun a ⟨_,
          ha2⟩ => hout_bm a (Or.inl (by omega))).trans
            (hqv0 i hi).1,
          (readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hout_bm a (Or.inl (by omega))).trans
            (hqv0 i hi).2⟩)
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
        exact ⟨(readPacked_congr hw (hidx := hj) fun a ⟨ha1,
          _⟩ => hout_bm a (Or.inr (by omega))).trans
            (hpool0 j hj).1,
          (readPacked_congr hw (hidx := hj) fun a ⟨ha1, _⟩ => hout_bm a (Or.inr (by omega))).trans
            (hpool0 j hj).2⟩)
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

/-- Frame helper for a single `writePacked` inside `[offQuotWhp, offBtMeta)` disjoint from
`offBktMeta`. -/
private theorem fastStep_pureArray {base c U V w n_max offW NW kW idxW valW : ℕ}
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
  rcases hrep with ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  rcases hunch with ⟨hsl_e, hbf_e, hdc_e, hpft_e, hce_e, hec_e, hrs_e, hsc_e, hdi_e, hrcs_e,
    hrsc_e, hric_e, hrcl_e, hbc_e, hbs_e, hlr_e, hli_e, hor_e, hoa_e, hoc_e, hoi_e, hrd_e,
    hrq_e, hdb_e⟩
  exact fastStep_nonSliceNonBuf hw rfl hseed hrep_orig hsl_e hbf_e
    (fun a ha => houtW a (by rcases ha with h1 | ⟨_, h2⟩ | ⟨h3, _⟩ | h4 <;> omega))
    (fun idx hidx _ => hbm_all idx hidx)
    (fun id hid => readPacked_congr hw (hidx := show id < 6 * qEpochWhp n_max + 6 by omega)
      fun a ⟨ha1, _⟩ => houtW a (Or.inr (by omega)))
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
    hqv hloc
    (fun b hb => by
      rw [hbc_e, hbs_e, hlr_e, hli_e, hor_e, hoa_e, hoc_e, hoi_e, hrd_e, hrq_e]
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hbmeta0 b hb
      exact ⟨(hbm_all _ (by omega)).trans r0, (hbm_all _ (by omega)).trans r1,
        (hbm_all _ (by omega)).trans r2, (hbm_all _ (by omega)).trans r3,
        (hbm_all _ (by omega)).trans r4, (hbm_all _ (by omega)).trans r5,
        (hbm_all _ (by omega)).trans r6, (hbm_all _ (by omega)).trans r7,
        (hbm_all _ (by omega)).trans r8, (hbm_all _ (by omega)).trans r9⟩)
    hbptr hpool
    (fun j hj => by
      rw [hdc_e] at hj; rw [hdb_e]
      exact (readPacked_congr hw (hidx :=
        show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega)
        fun a ⟨ha1, _⟩ => houtW a (Or.inr (by omega))).trans (hdirty0 j hj))

/-- Read `fs.locState b loc` (`d = (((cp, base), b), loc)`). -/
@[irreducible] def readFastLocGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) =>
    readLocStateGenProg (((base, wpOffLocState cp), (wpTotalLoc cp, wpW cp)), (b, loc))

theorem realizes_readFastLocGen :
    Realizes .exact readFastLocGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), loc) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ loc < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold readFastLocGenProg
  have hrl := realizes_readLocStateGen
  realize
  rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hloc⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hlog_w := henv.log_lt_w
  have hlog_ge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  have h2tl := (large_index_bounds hth).2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
  simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_offLocState hth, wp_large_w hth]
    at hb hloc ⊢
  exact ⟨numBucketsWhp n_max, rfl, by omega, henv.fits_of_le_n_max (by omega),
    hb, hloc, henv.fits_largeSpace.of_le (by omega)⟩

theorem readFastLocGenProg_spec {c U V w n_max base b loc : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.locState b loc ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hst, hres, hmc, hvp⟩ := readLocStateGenProg_spec henv hb hloc (s := s)
  have hls := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb loc hloc
  unfold readFastLocGenProg
  simp only [wp_large_offLocState hth, wp_large_totalLoc hth, wp_large_w hth]
  exact ⟨hst, hres.trans hls, hmc, hvp⟩

/-- Write `fs.locState b loc := tag` (`tag < 4`, `d = ((((cp, base), b), loc), tag)`). -/
@[irreducible] def writeFastLocGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), loc), tag) =>
    writeLocStateGenProg ((((base, wpOffLocState cp), (wpTotalLoc cp, wpW cp)), (b, loc)), tag)

theorem realizes_writeFastLocGen :
    Realizes .exact writeFastLocGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ loc < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold writeFastLocGenProg
  have hwl := realizes_writeLocStateGen
  realize
  rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc⟩, tag⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hloc⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hlog_w := henv.log_lt_w
  have hlog_ge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  have h2tl := (large_index_bounds hth).2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
  simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_offLocState hth, wp_large_w hth]
    at hb hloc ⊢
  exact ⟨numBucketsWhp n_max, rfl, by omega, henv.fits_of_le_n_max (by omega),
    hb, hloc, henv.fits_largeSpace.of_le (by omega)⟩

theorem writeFastLocGenProg_fastStep {c U V w n_max base b loc tag : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) (htag : tag < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeFastLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc), tag)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        locState := Function.update fs.locState b (Function.update (fs.locState b) loc tag) }
      s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  obtain ⟨hst, hmc, hvp⟩ := writeLocStateGenProg_spec henv hb hloc (val := tag) (s := s)
  unfold writeFastLocGenProg
  simp only [wp_large_offLocState hth, wp_large_totalLoc hth, wp_large_w hth]
  rw [hst]
  set idxW := b * totalLocalCoordsWhp n_max + loc
  have hidxW : idxW < numBucketsWhp n_max * totalLocalCoordsWhp n_max :=
    mul_add_lt_mul_bound hb hloc
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hmc, hvp, fastStep_pureArray hw hidxW (by omega) (by omega) (Or.inl (by omega))
    hseed hrep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans
        (hqv0 i hi).1,
      (readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
    (fun b' hb' loc' hl' => ?_)
    (fun b' hb' k hk =>
      (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb' hk) hidxW
        (Or.inr (by omega))).trans (hbptr0 b' hb' k hk))
    (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
        (hpool0 j hj).1,
      (readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
        (hpool0 j hj).2⟩)⟩
  dsimp only
  by_cases hbl : b' = b ∧ loc' = loc
  · rcases hbl with ⟨rfl, rfl⟩
    simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem idxW htag
  · have hne : b' * totalLocalCoordsWhp n_max + loc' ≠ idxW :=
      fun heq => hbl (mul_add_inj_right hl' hloc heq)
    rw [readPacked_writePacked_of_ne hw s.mem hne tag, hloc0 b' hb' loc' hl']
    by_cases hbb : b' = b
    · subst hbb
      have hll : loc' ≠ loc := fun h => hbl ⟨rfl, h⟩
      simp [hll]
    · simp [hbb]

/-- Read `fs.quotArr p` (`p < n_max`, `d = ((cp, base), p)`). -/
@[irreducible] def readQuotGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), p) =>
    readPackedGenProg (((base, wpOffQuot cp), (wpQuotBits cp, wpW cp)), p)

theorem realizes_readQuotGen :
    Realizes .exact readQuotGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), p) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold readQuotGenProg
  have hrp := realizes_readPackedGen
  realize
  rcases d with ⟨⟨cp, base⟩, p⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hqb : quotBitsWhp U n_max ≤ w := (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  simp only [wp_large_nMax hth, wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth] at hp ⊢
  exact packed_safe_true henv hqb hp (WhpLargeEnv.seg_end_le c U V w n_max).1

theorem readQuotGenProg_spec {c U V w n_max base p : ℕ} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hp : p < n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readQuotGenProg ((mkWhpCoreParams c U V w n_max, base), p)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.quotArr p ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).1
  have hle : base + offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readQuotGenProg
  simp only [wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).1, rfl, validProg_readPacked hw hp hle⟩

/-- Write `fs.quotArr p := q_val` (`p < n_max`, `d = (((cp, base), p), q_val)`). -/
@[irreducible] def writeQuotGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), p), q_val) =>
    writePackedGenProg ((((base, wpOffQuot cp), (wpQuotBits cp, wpW cp)), p), q_val)

theorem realizes_writeQuotGen :
    Realizes .exact writeQuotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), p), _) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold writeQuotGenProg
  have hwp := realizes_writePackedGen
  realize
  rcases d with ⟨⟨⟨cp, base⟩, p⟩, q_val⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hqb : quotBitsWhp U n_max ≤ w := (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  simp only [wp_large_nMax hth, wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth] at hp ⊢
  exact packed_safe_true henv hqb hp (WhpLargeEnv.seg_end_le c U V w n_max).1

theorem writeQuotGenProg_fastStep {c U V w n_max base p q_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hp : p < n_max) (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeQuotGenProg (((mkWhpCoreParams c U V w n_max, base), p), q_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with quotArr := Function.update fs.quotArr p q_val } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hqb : quotBitsWhp U n_max ≤ w := (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).1
  have hle : base + offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold writeQuotGenProg
  simp only [wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hqb hp hle,
    fastStep_pureArray hw hp le_rfl (by omega) (Or.inl (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨?_,
        (readPacked_writePacked_disjoint hw hi hp (Or.inr (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hp
          (Or.inr (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hp
          (Or.inr (by omega))).trans (hbptr0 b hb k hk))
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans (hpool0 j hj).2⟩)⟩
  by_cases hip : i = p
  · subst hip; simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem i hq_lt
  · simp only [Function.update_of_ne hip]
    exact (readPacked_writePacked_of_ne hw s.mem hip q_val).trans (hqv0 i hi).1

/-- Read `fs.valArr p` (`p < n_max`, `d = ((cp, base), p)`). -/
@[irreducible] def readValGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), p) =>
    readPackedGenProg (((base, wpOffVal cp), (wpValBits cp, wpW cp)), p)

theorem realizes_readValGen :
    Realizes .exact readValGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), p) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold readValGenProg
  have hrp := realizes_readPackedGen
  realize
  rcases d with ⟨⟨cp, base⟩, p⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hvb : valBits V ≤ w := valBits_le_w henv.2.2.2.2.2.2.1
  simp only [wp_large_nMax hth, wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth] at hp ⊢
  exact packed_safe_true henv hvb hp (WhpLargeEnv.seg_end_le c U V w n_max).2.1

theorem readValGenProg_spec {c U V w n_max base p : ℕ} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hp : p < n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readValGenProg ((mkWhpCoreParams c U V w n_max, base), p)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.valArr p ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.1
  have hle : base + offValWhp c U w n_max + packedWords n_max (valBits V) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readValGenProg
  simp only [wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).2, rfl, validProg_readPacked hw hp hle⟩

/-- Write `fs.valArr p := v_val` (`p < n_max`, `d = (((cp, base), p), v_val)`). -/
@[irreducible] def writeValGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), p), v_val) =>
    writePackedGenProg ((((base, wpOffVal cp), (wpValBits cp, wpW cp)), p), v_val)

theorem realizes_writeValGen :
    Realizes .exact writeValGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), p), _) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold writeValGenProg
  have hwp := realizes_writePackedGen
  realize
  rcases d with ⟨⟨⟨cp, base⟩, p⟩, v_val⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hvb : valBits V ≤ w := valBits_le_w henv.2.2.2.2.2.2.1
  simp only [wp_large_nMax hth, wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth] at hp ⊢
  exact packed_safe_true henv hvb hp (WhpLargeEnv.seg_end_le c U V w n_max).2.1

theorem writeValGenProg_fastStep {c U V w n_max base p v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hp : p < n_max) (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeValGenProg (((mkWhpCoreParams c U V w n_max, base), p), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with valArr := Function.update fs.valArr p v_val } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hvb : valBits V ≤ w := valBits_le_w henv.2.2.2.2.2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.1
  have hle : base + offValWhp c U w n_max + packedWords n_max (valBits V) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold writeValGenProg
  simp only [wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hvb hp hle,
    fastStep_pureArray hw hp (by omega) (by omega) (Or.inl (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hp (Or.inl (by omega))).trans
          (hqv0 i hi).1, ?_⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hp
          (Or.inr (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hp
          (Or.inr (by omega))).trans (hbptr0 b hb k hk))
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans (hpool0 j hj).2⟩)⟩
  by_cases hip : i = p
  · subst hip; simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem i hv_lt
  · simp only [Function.update_of_ne hip]
    exact (readPacked_writePacked_of_ne hw s.mem hip v_val).trans (hqv0 i hi).2

/-- Read `fs.backPtr b k` (`b < M`, `k < capBackWhp n_max`, `d = (((cp, base), b), k)`). -/
@[irreducible] def readBackPtrGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), k) => do
    let idx ← pure (b * wpCapBack cp + k)
    readPackedGenProg (((base, wpOffBackPtr cp), (wpGlobalPtrBits cp, wpW cp)), idx)

theorem realizes_readBackPtrGen :
    Realizes .exact readBackPtrGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), k) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp)
      (fun _ _ => 0) := by
  unfold readBackPtrGenProg
  have hrp := realizes_readPackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, k⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hk⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hmcb := (large_index_bounds hth).1
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    simp only [wp_large_M hth, wp_large_capBack hth, wp_large_offBackPtr hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at hb hk ⊢
    have hidx := mul_add_lt_mul_bound hb hk
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact packed_safe_true henv hgk hidx
        (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  )

theorem readBackPtrGenProg_spec {c U V w n_max base b k : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hk : k < capBackWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readBackPtrGenProg (((mkWhpCoreParams c U V w n_max, base), b), k)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.backPtr b k ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hidx := mul_add_lt_mul_bound hb hk
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  have hle : base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readBackPtrGenProg
  simp only [wp_large_capBack hth, wp_large_offBackPtr hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb k hk), rfl, validProg_readPacked hw hidx hle⟩

/-- Write `fs.backPtr b k := pSlot` (`d = ((((cp, base), b), k), pSlot)`). -/
@[irreducible] def writeBackPtrGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), k), pSlot) => do
    let idx ← pure (b * wpCapBack cp + k)
    writePackedGenProg ((((base, wpOffBackPtr cp), (wpGlobalPtrBits cp, wpW cp)), idx), pSlot)

theorem realizes_writeBackPtrGen :
    Realizes .exact writeBackPtrGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), k), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp)
      (fun _ _ => 0) := by
  unfold writeBackPtrGenProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, k⟩, pSlot⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hk⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hmcb := (large_index_bounds hth).1
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    simp only [wp_large_M hth, wp_large_capBack hth, wp_large_offBackPtr hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at hb hk ⊢
    have hidx := mul_add_lt_mul_bound hb hk
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact packed_safe_true henv hgk hidx
        (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  )

theorem writeBackPtrGenProg_fastStep {c U V w n_max base b k pSlot : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hk : k < capBackWhp n_max) (hp_le : pSlot ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeBackPtrGenProg ((((mkWhpCoreParams c U V w n_max, base), b), k), pSlot)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with backPtr := Function.update fs.backPtr b (Function.update (fs.backPtr b) k pSlot) }
      s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hp_g : pSlot < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max hp_le
  set idxW := b * capBackWhp n_max + k
  have hidxW := mul_add_lt_mul_bound hb hk
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  have hle : base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold writeBackPtrGenProg
  simp only [wp_large_capBack hth, wp_large_offBackPtr hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hgk hidxW hle,
    fastStep_pureArray hw hidxW (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b' hb' loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb' hl) hidxW
          (Or.inl (by omega))).trans (hloc0 b' hb' loc hl))
      (fun b' hb' k' hk' => ?_)
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
          (hpool0 j hj).2⟩)⟩
  dsimp only
  by_cases hbk : b' = b ∧ k' = k
  · rcases hbk with ⟨rfl, rfl⟩
    simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem idxW hp_g
  · have hne : b' * capBackWhp n_max + k' ≠ idxW :=
      fun heq => hbk (mul_add_inj_right hk' hk heq)
    rw [readPacked_writePacked_of_ne hw s.mem hne pSlot, hbptr0 b' hb' k' hk']
    by_cases hbb : b' = b
    · subst hbb
      have hkk : k' ≠ k := fun h => hbk ⟨rfl, h⟩
      simp [hkk]
    · simp [hbb]

/-- Read `fs.poolFreeStack j` (`j < poolSizeWhp n_max`, `d = ((cp, base), j)`). -/
@[irreducible] def readPoolFreeStackGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), j) =>
    readPackedGenProg (((base, wpOffPoolFreeStack cp), (wpGlobalPtrBits cp, wpW cp)), j)

theorem realizes_readPoolFreeStackGen :
    Realizes .exact readPoolFreeStackGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), j) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold readPoolFreeStackGenProg
  have hrp := realizes_readPackedGen
  realize
  rcases d with ⟨⟨cp, base⟩, j⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_poolSize hth, wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hj ⊢
  exact packed_safe_true henv hgk hj (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1

theorem readPoolFreeStackGenProg_spec {c U V w n_max base j : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hj : j < poolSizeWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readPoolFreeStackGenProg ((mkWhpCoreParams c U V w n_max, base), j)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.poolFreeStack j ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
  have hle : base + offPoolFreeStack c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readPoolFreeStackGenProg
  simp only [wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).1, rfl, validProg_readPacked hw hj hle⟩

/-- Write `fs.poolFreeStack j := pSlot`
(`j < poolSizeWhp n_max`, `d = (((cp, base), j), pSlot)`). -/
@[irreducible] def writePoolFreeStackGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), j), pSlot) =>
    writePackedGenProg ((((base, wpOffPoolFreeStack cp), (wpGlobalPtrBits cp, wpW cp)), j), pSlot)

theorem realizes_writePoolFreeStackGen :
    Realizes .exact writePoolFreeStackGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), j), _) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold writePoolFreeStackGenProg
  have hwp := realizes_writePackedGen
  realize
  rcases d with ⟨⟨⟨cp, base⟩, j⟩, pSlot⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_poolSize hth, wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hj ⊢
  exact packed_safe_true henv hgk hj (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1

theorem writePoolFreeStackGenProg_fastStep {c U V w n_max base j pSlot : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hj : j < poolSizeWhp n_max) (hp_le : pSlot ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writePoolFreeStackGenProg (((mkWhpCoreParams c U V w n_max, base), j), pSlot)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with poolFreeStack := Function.update fs.poolFreeStack j pSlot } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hp_g : pSlot < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max hp_le
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
  have hle : base + offPoolFreeStack c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold writePoolFreeStackGenProg
  simp only [wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hgk hj hle,
    fastStep_pureArray hw hj (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hj
          (Or.inl (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hj
          (Or.inl (by omega))).trans (hbptr0 b hb k hk))
      (fun j' hj' => ⟨?_,
        (readPacked_writePacked_disjoint hw hj' hj (Or.inr (by omega))).trans (hpool0 j' hj').2⟩)⟩
  by_cases hjj : j' = j
  · subst hjj; simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem j' hp_g
  · simp only [Function.update_of_ne hjj]
    exact (readPacked_writePacked_of_ne hw s.mem hjj pSlot).trans (hpool0 j' hj').1

/-- Write `fs.poolOwner j := enc` (`j < poolSizeWhp n_max`, `d = (((cp, base), j), enc)`). -/
@[irreducible] def writePoolOwnerGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), j), enc) =>
    writePackedGenProg ((((base, wpOffPoolOwner cp), (wpGlobalPtrBits cp, wpW cp)), j), enc)

theorem realizes_writePoolOwnerGen :
    Realizes .exact writePoolOwnerGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), j), _) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold writePoolOwnerGenProg
  have hwp := realizes_writePackedGen
  realize
  rcases d with ⟨⟨⟨cp, base⟩, j⟩, enc⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_poolSize hth, wp_large_offPoolOwner hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hj ⊢
  exact packed_safe_true henv hgk hj (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1

theorem writePoolOwnerGenProg_fastStep {c U V w n_max base j enc : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hj : j < poolSizeWhp n_max) (henc_le : enc ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writePoolOwnerGenProg (((mkWhpCoreParams c U V w n_max, base), j), enc)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with poolOwner := Function.update fs.poolOwner j enc } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have henc_g : enc < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max henc_le
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1
  have hle : base + offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold writePoolOwnerGenProg
  simp only [wp_large_offPoolOwner hth, wp_large_globalPtrBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hgk hj hle,
    fastStep_pureArray hw hj (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hj
          (Or.inl (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hj
          (Or.inl (by omega))).trans (hbptr0 b hb k hk))
      (fun j' hj' => ⟨(readPacked_writePacked_disjoint hw hj' hj (Or.inl (by omega))).trans
          (hpool0 j' hj').1, ?_⟩)⟩
  by_cases hjj : j' = j
  · subst hjj; simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem j' henc_g
  · simp only [Function.update_of_ne hjj]
    exact (readPacked_writePacked_of_ne hw s.mem hjj enc).trans (hpool0 j' hj').2

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
    | exact packed_safe_true henv hgk (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by
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
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hle : base + offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readDirtyBucketGenProg
  simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj), rfl,
    validProg_readPacked hw hidx hle⟩

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
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hrh_st, hrh_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
      (s := s) (by dsimp [hdrDirtyCount]; omega)
    simp only [hrh_st, hrh_res] at *
    simp only [wp_large_qEpoch hth, wp_large_offTrieItems0 hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hdc_lt ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact packed_safe_true henv hgk
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
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hle : base + offTrieItems0 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  rcases hrep with ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le0, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv0, hloc0, hbmeta0, hbptr0, hpool0, hsl0, hbuf0, hbuf1, hdirty0⟩
  obtain ⟨hrh_st, hrh_res, hrh_mc, hrh_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
    (s := s) (by dsimp [hdrDirtyCount]; omega)
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
    exact validProg_bind (validProg_writePacked hw hgk hidxW hle) hwh_vp
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
      (fun b' hb' => by
        obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hbmeta0 b' hb'
        have h9 : ∀ k < 10,
            readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w m2 (16 * b' + k) =
              readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
                (16 * b' + k) :=
          fun k hk => hrp_pre (show 16 * b' + k < 16 * numBucketsWhp n_max by omega)
            (by omega) (by omega)
        exact ⟨(h9 0 (by decide)).trans r0, (h9 1 (by decide)).trans r1,
          (h9 2 (by decide)).trans r2, (h9 3 (by decide)).trans r3,
          (h9 4 (by decide)).trans r4, (h9 5 (by decide)).trans r5,
          (h9 6 (by decide)).trans r6, (h9 7 (by decide)).trans r7,
          (h9 8 (by decide)).trans r8, (h9 9 (by decide)).trans r9⟩)
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

/-! ## Section 4: Composite Fast-Mode Helpers (`physSlot`, `rKeyAt`, `fpAt`, `inLiveTree`,
`matchesKey`, `rebActiveB`, `fastFindLoc`, `fastQuery`) -/

/-- Compute `fs.physSlot n_max b loc` (`d = (((cp, base), b), loc)`). -/
@[irreducible] def physSlotGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) => do
    let cf ← pure (wpCapFront cp)
    if loc < cf then
      pure (b * cf + loc)
    else do
      let k ← pure (loc - cf)
      let pSlot ← readBackPtrGenProg (((cp, base), b), k)
      pure (wpFrontTotal cp + pSlot)

/-- Precondition for `physSlotGenProg`: `(b, loc)` in bounds and backyard pointer `< poolSize`. -/
@[expose] def PhysSlotPre (w : ℕ) : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), b), loc), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max ∧
      (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)

theorem realizes_physSlotGen :
    Realizes .exact physSlotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PhysSlotPre
      (fun _ _ => 0) := by
  unfold physSlotGenProg
  have hrb := realizes_readBackPtrGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hloc, hbp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hps_eq := (large_index_bounds hth).2.1
    have hcb : capFrontWhp n_max ≤ loc → loc - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hloc; omega
    simp only [wp_large_capFront hth, wp_large_frontTotal hth, wp_large_M hth,
      wp_large_capBack hth] at *
    first
    | (have hlt : b * capFrontWhp n_max + loc < numBucketsWhp n_max * capFrontWhp n_max :=
         mul_add_lt_mul_bound hb (by omega)
       exact henv.fits_of_le_n_max (by omega))
    | omega
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (obtain ⟨_, hres, _, _⟩ := readBackPtrGenProg_spec henv hb (hcb (by omega)) hrep (s := s)
       rw [hres]
       have hp := hbp_lt (by omega)
       exact henv.fits_of_le_n_max (by omega))
  )

theorem physSlotGenProg_spec {c U V w n_max base b loc : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp_lt : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := physSlotGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.physSlot n_max b loc ∧
    fs.physSlot n_max b loc < n_max ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hps_eq := (large_index_bounds hth).2.1
  unfold physSlotGenProg FastState.physSlot
  simp only [wp_large_capFront hth, wp_large_frontTotal hth, pure_bind]
  by_cases hcf : loc < capFrontWhp n_max
  · simp only [hcf, ↓reduceIte]
    have hlt := mul_add_lt_mul_bound hb hcf
    exact ⟨rfl, rfl, by omega, Nat.zero_le 2, validProg_pure _⟩
  · simp only [hcf, ↓reduceIte]
    have hk : loc - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hloc; omega
    obtain ⟨hst, hres, hmc, hvp⟩ := readBackPtrGenProg_spec henv hb hk hrep (s := s)
    have hp := hbp_lt (Nat.not_lt.mp hcf)
    refine ⟨?_, ?_, by omega, ?_, ?_⟩
    · rw [clientState_bind, hst]; rfl
    · rw [clientResult_bind, hst, hres]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst, hmc]; exact le_rfl
    · refine validProg_bind hvp ?_; rw [hst]; exact validProg_pure _

/-- Compute `fs.rKeyAt c U n_max θ b loc` (`d = (((wp, base), b), loc)`). -/
@[irreducible] def rKeyAtGenProg : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc) => do
    let (cp, _) := wp
    let p ← physSlotGenProg (((cp, base), b), loc)
    let q ← readQuotGenProg ((cp, base), p)
    let hrt ← mkHashRtGenProg (wp, base)
    rKeyOfQuotRtProg ((hrt, b), q)

/-- Precondition for `rKeyAtGenProg` and `fpAtGenProg` on coordinate `(b, loc)`. -/
@[expose] def CoordHashPre (w : ℕ) : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((wp, base), b), loc), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (∀ p < n_max, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max ∧
      (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)

theorem realizes_rKeyAtGen :
    Realizes .exact rKeyAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold rKeyAtGenProg
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_rKeyOfQuotRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hcp_eq : wp.1 = mkWhpCoreParams c U V w n_max := by
      rw [heq_wp]; simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    obtain ⟨hrq_st, hrq_res, _, _⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hcp_eq] at *
    simp only [heq_wp] at *
    simp only [hps_st, hps_res, hrq_st, hrq_res, hmh_st, hmh_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed, hq_all _ hps_lt⟩
  )

theorem rKeyAtGenProg_spec {c U V w n_max base b loc : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := rKeyAtGenProg (((mkWhpParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.rKeyAt c U n_max θ b loc ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hrq_st, hrq_res, hrq_mc, hrq_vp⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyOfQuotRtProg_spec (b := b) (q := fs.quotArr (fs.physSlot n_max b loc)) henv hseed (s := s)
  unfold rKeyAtGenProg
  change (let p0 := mkWhpParams c U V w n_max; _)
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hps_st, hps_res, clientState_bind, hrq_st, hrq_res,
      clientState_bind, hmh_st, hmh_res, hrk_st]
  · rw [clientResult_bind, hps_st, hps_res, clientResult_bind, hrq_st, hrq_res,
      clientResult_bind, hmh_st, hmh_res, hrk_res]
    rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res, hrq_st, hrq_res, hmh_st, hmh_res, hrq_mc, hmh_mc]
    omega
  · refine validProg_bind hps_vp ?_
    rw [hps_st, hps_res]
    refine validProg_bind hrq_vp ?_
    rw [hrq_st, hrq_res]
    refine validProg_bind hmh_vp ?_
    rw [hmh_st, hmh_res]
    exact hrk_vp

/-- Compute `fs.fpAt c U n_max θ salt b loc` (`d = ((((wp, base), salt), b), loc)`). -/
@[irreducible] def fpAtGenProg : (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), salt), b), loc) => do
    let (cp, _) := wp
    let p ← physSlotGenProg (((cp, base), b), loc)
    let q ← readQuotGenProg ((cp, base), p)
    let hrt ← mkHashRtGenProg (wp, base)
    fpOfQuotRtProg (((hrt, salt), b), q)

theorem realizes_fpAtGen :
    Realizes .exact fpAtGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), _), b), loc) s => CoordHashPre w (((wp, base), b), loc) s)
      (fun _ _ => 0) := by
  unfold fpAtGenProg
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfQuotRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, salt⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hcp_eq : wp.1 = mkWhpCoreParams c U V w n_max := by
      rw [heq_wp]; simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    obtain ⟨hrq_st, hrq_res, _, _⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hcp_eq] at *
    simp only [heq_wp] at *
    simp only [hps_st, hps_res, hrq_st, hrq_res, hmh_st, hmh_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed, hq_all _ hps_lt⟩
  )

theorem fpAtGenProg_spec {c U V w n_max base salt b loc : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := fpAtGenProg ((((mkWhpParams c U V w n_max, base), salt), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.fpAt c U n_max θ salt b loc ∧
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hrq_st, hrq_res, hrq_mc, hrq_vp⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfQuotRtProg_spec (salt := salt) (b := b) (q := fs.quotArr (fs.physSlot n_max b loc))
      henv hseed (s := s)
  unfold fpAtGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hps_st, hps_res, clientState_bind, hrq_st, hrq_res,
      clientState_bind, hmh_st, hmh_res, hfp_st]
  · rw [clientResult_bind, hps_st, hps_res, clientResult_bind, hrq_st, hrq_res,
      clientResult_bind, hmh_st, hmh_res, hfp_res]
    rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res, hrq_st, hrq_res, hmh_st, hmh_res, hrq_mc, hmh_mc]
    omega
  · refine validProg_bind hps_vp ?_
    rw [hps_st, hps_res]
    refine validProg_bind hrq_vp ?_
    rw [hrq_st, hrq_res]
    refine validProg_bind hmh_vp ?_
    rw [hmh_st, hmh_res]
    exact hfp_vp

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

/-- Check `fs.matchesKey n_max b q_val b_cand loc`
(`d = (((cp, base), (b, q_val)), (b_cand, loc))`). -/
@[irreducible] private def matchesKeyGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, base), (b, q_val)), (b_cand, loc)) => do
    let z0 ← pure 0
    let z1 ← pure 1
    if b_cand = b then do
      let cnt ← readBktFieldGenProg (((cp, base), b), z0)
      if loc < cnt then do
        let p ← physSlotGenProg (((cp, base), b), loc)
        let q_got ← readQuotGenProg ((cp, base), p)
        if q_got = q_val then pure z1 else pure z0
      else
        pure z0
    else
      pure z0

/-- Precondition for `matchesKeyGenProg`. -/
private def MatchesKeyPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, base), (b, _)), (_, _)), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_matchesKeyGen :
    Realizes .exact matchesKeyGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      MatchesKeyPre
      (fun _ _ => 0) := by
  unfold matchesKeyGenProg
  have hrb := realizes_readBktFieldGen
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, q_val⟩⟩, ⟨b_cand, loc⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hrb_st, hrb_res, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 0 < 10)
      hrep (s := s)
    dsimp only [getBktField] at hrb_res
    simp only [hrb_st, hrb_res, wp_large_M hth, wp_large_nMax hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | refine ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, by omega, fun hcf => hbp_v _ (by omega)⟩
    | (obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb (by omega : loc < _)
         (fun hcf => hbp_v _ (by omega)) hrep (s := s)
       simp only [hps_st, hps_res] at *
       exact hps_lt)
  )

private theorem matchesKeyGenProg_spec {c U V w n_max base b q_val b_cand loc : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := matchesKeyGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (b_cand, loc))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.matchesKey n_max b q_val b_cand loc then 1 else 0) ∧
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold matchesKeyGenProg FastState.matchesKey
  simp only [pure_bind]
  by_cases hbb : b_cand = b
  · simp only [hbb, ↓reduceIte, beq_self_eq_true, Bool.true_and]
    obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc_res
    by_cases hlt : loc < fs.bktCount b
    · obtain ⟨hp_st, hp_res, hp_lt, hp_mc, hp_vp⟩ :=
        physSlotGenProg_spec henv hb (hlt.trans_le hcnt_le) (fun hcf => hbp_v _ (by omega))
          hrep (s := s)
      obtain ⟨hq_st, hq_res, hq_mc, hq_vp⟩ := readQuotGenProg_spec henv hp_lt hrep (s := s)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hc_st, hc_res]; simp only [hlt, ↓reduceIte]
        rw [clientState_bind, hp_st, hp_res, clientState_bind, hq_st, hq_res]
        split_ifs <;> rfl
      · rw [clientResult_bind, hc_st, hc_res]; simp only [hlt, ↓reduceIte, decide_true,
          Bool.true_and]
        rw [clientResult_bind, hp_st, hp_res, clientResult_bind, hq_st, hq_res]
        by_cases hqq : fs.quotArr (fs.physSlot n_max b loc) = q_val <;> simp [hqq]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hc_st, hc_res, hc_mc]; simp only [hlt, ↓reduceIte, memoryCost_bind]
        rw [hp_st, hp_res, hq_st, hq_res, hq_mc]
        split_ifs <;> (change 2 + (_ + (2 + 0)) ≤ 6; omega)
      · refine validProg_bind hc_vp ?_
        rw [hc_st, hc_res]; simp only [hlt, ↓reduceIte]
        refine validProg_bind hp_vp ?_
        rw [hp_st, hp_res]
        refine validProg_bind hq_vp ?_
        rw [hq_st]
        split_ifs <;> exact validProg_pure _
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hc_st, hc_res, ite_eq_right hlt]; rfl
      · rw [clientResult_bind, hc_st, hc_res, ite_eq_right hlt]; simp [hlt]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hc_st, hc_res, hc_mc, ite_eq_right hlt]; simp
      · refine validProg_bind hc_vp ?_
        rw [hc_st, hc_res, ite_eq_right hlt]; exact validProg_pure _
  · rw [ite_eq_right hbb]
    exact ⟨rfl, by simp [hbb], Nat.zero_le 6, validProg_pure _⟩

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
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcs_h : ∀ off < 32, ∀ s',
        (Memory.spec 0).clientState s' (readHdrProg (base, off)) = s' :=
      fun off hoff s' => (readHdrProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max)
        (by omega)).1
    have hcr_h : ∀ off < 32, ∀ s',
        (Memory.spec 0).clientResult s' (readHdrProg (base, off)) = s'.mem (base + off) :=
      fun off hoff s' => (readHdrProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max)
        (by omega)).2.1
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
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  rcases hrep with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hqv, hloc, hbmeta, hbptr, hpool, hsl, hbuf0, hbuf1, hdirty⟩
  have hrep_orig : FastMemRep base c U V w n_max fs s.mem :=
    ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv, hloc, hbmeta, hbptr, hpool, hsl, hbuf0, hbuf1, hdirty⟩
  have hrh : ∀ off < 32,
      (Memory.spec 0).clientState s (readHdrProg (base, off)) = s ∧
      (Memory.spec 0).clientResult s (readHdrProg (base, off)) = s.mem (base + off) ∧
      memoryCost (readHdrProg (base, off)) s = 1 ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (readHdrProg (base, off)) :=
    fun off hoff => readHdrProg_spec (by omega)
  obtain ⟨hst4, hres4, hmc4, hvp4⟩ := hrh hdrRebStage (by decide)
  obtain ⟨hst7, hres7, hmc7, hvp7⟩ := hrh hdrDirtyIdx (by decide)
  obtain ⟨hst6, hres6, hmc6, hvp6⟩ := hrh hdrDirtyCount (by decide)
  obtain ⟨hst8, hres8, hmc8, hvp8⟩ := hrh hdrRebCandSalt (by decide)
  obtain ⟨hst11, hres11, hmc11, hvp11⟩ := hrh hdrRebCollision (by decide)
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

/-! ### `fastFindLocBqGenProg` and `fastQueryGenProg` -/

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

/-- Probe epoch buffer `ep` at `rKey` and verify `matchesKey`
(`d = ((((cp, base), ep), (b, q_val)), rKey)`). -/
@[irreducible] private def probeBufCandGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((((cp, base), ep), (b, q_val)), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let lk ← bufLookupGenProg (((cp, base), ep), rKey)
    let (hit, b_loc) := lk
    if hit = z1 then do
      let ok ← matchesKeyGenProg (((cp, base), (b, q_val)), b_loc)
      if ok = z1 then pure (z1, b_loc.2) else pure (z0, z0)
    else
      pure (z0, z0)

/-- Precondition for `probeBufCandGenProg`. -/
private def ProbeBufCandPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((((cp, base), ep), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (mapFn : ℕ → Option (ℕ × ℕ)),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (ep = 0 ∨ ep = 1) ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeBufCandGen :
    Realizes .exact probeBufCandGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeBufCandPre
      (fun _ _ => 0) := by
  unfold probeBufCandGenProg
  have hbl := realizes_bufLookupGen
  have hmk := realizes_matchesKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, ep⟩, ⟨b, q_val⟩⟩, rKey⟩
    try dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, mapFn, henv, rfl, hrep, hep, hv, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hbl_st, _, _, _⟩ :=
      bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
    simp only [hbl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs.buf ep, mapFn, henv, rfl, hep, hrep.buf_rep hep, hv⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩
  )

private theorem probeBufCandGenProg_spec {c U V w n_max base ep b q_val rKey : ℕ}
    {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := probeBufCandGenProg
      ((((mkWhpCoreParams c U V w n_max, base), ep), (b, q_val)), rKey)
    let cand : Option ℕ :=
      match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with
      | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
      | none => none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 14 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hl_st, hl_res, hl_mc, hl_vp⟩ :=
    bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
  dsimp only
  unfold probeBufCandGenProg
  simp only [pure_bind]
  cases hlk : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with
  | none =>
    rw [hlk] at hl_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hl_st, hl_res]; rfl
    · rw [clientResult_bind, hl_st, hl_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hl_st, hl_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hl_vp ?_
      rw [hl_st, hl_res]; exact validProg_pure _
  | some p =>
    rcases p with ⟨b', loc⟩
    rw [hlk] at hl_res
    obtain ⟨hm_st, hm_res, hm_mc, hm_vp⟩ :=
      matchesKeyGenProg_spec henv hrep hb hcnt_le hbp_v (q_val := q_val) (b_cand := b')
        (loc := loc) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hl_st, hl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientState_bind, hm_st]; split_ifs <;> rfl
    · rw [clientResult_bind, hl_st, hl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientResult_bind, hm_st, hm_res]
      cases hmk : fs.matchesKey n_max b q_val b' loc <;> simp
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hl_st, hl_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
      rw [hm_st]
      have hm_mc' : memoryCost (matchesKeyGenProg
          (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (b', loc))) s ≤ 6 := hm_mc
      split_ifs <;> (change memoryCost _ s + (memoryCost _ s + 0) ≤ _; omega)
    · refine validProg_bind hl_vp ?_
      rw [hl_st, hl_res]; dsimp only; simp only [↓reduceIte]
      refine validProg_bind hm_vp ?_
      rw [hm_st]; split_ifs <;> exact validProg_pure _

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

/-- Lookup `fpOfSalt` in `liveSlice[b]` (`d = ((wp, base), (b, u_val))`). -/
@[irreducible] private def probeLiveLookupGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp, base), (b, u_val)) => do
    let si ← readLiveSaltIdxGenProg ((wp.1, base), b)
    let hrt ← mkHashRtGenProg (wp, base)
    let fp ← fpOfSaltOptRtProg ((hrt, si.1), u_val)
    btreeLookupGenProg (((wp.1, base), si.2), fp)

private theorem realizes_probeLiveLookupGen :
    Realizes .exact probeLiveLookupGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (mapFn : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn)
      (fun _ _ => 0) := by
  unfold probeLiveLookupGenProg
  have hrs := realizes_readLiveSaltIdxGen
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfSaltOptRt
  have hbt := realizes_btreeLookupGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, heq_wp, hseed, hrep,
      hb, hlr, hins, hv_sl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hfp_lt : (if hs : fs.bktSalt b < sMaxWhp c n_max then
        if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
       else 0) < 2 ^ fpBitsWhp n_max := fpOfSaltOpt_lt c U n_max _ _ θ.2
    simp only [hcp_eq] at *
    simp only [hrs_st, hrs_res, hmh_st, hmh_res, hfp_st, hfp_res] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), mapFn,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_sl, hfp_lt⟩
  )

private theorem probeLiveLookupGenProg_spec {c U V w n_max base b u_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn) :
    let prog := probeLiveLookupGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))
    let fp := if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
     else 0
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
       | some loc => (1, loc)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 266 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
  set fp := if hs : fs.bktSalt b < sMaxWhp c n_max then
    if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
   else 0
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpOfSaltOpt_lt c U n_max _ _ θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.liveSliceIdx; omega
  obtain ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ :=
    btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt_res
  dsimp only
  unfold probeLiveLookupGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
      clientState_bind, hfp_st, hfp_res, hbt_st]
  · rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
      clientResult_bind, hfp_st, hfp_res, hbt_res]
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrs_st, hrs_res, hrs_mc, hmh_st, hmh_res, hmh_mc, hfp_st, hfp_res]
    have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.bktSalt b),
        u_val)) s ≤ hashEvalCostWhp c := hfp_mc
    have hbt_mc' : memoryCost (btreeLookupGenProg (((mkWhpCoreParams c U V w n_max, base),
        fs.liveSliceIdx b), fp)) s ≤ 262 := hbt_mc
    dsimp only
    omega
  · refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    exact hbt_vp

/-- Probe `liveSlice[b]` for key `u_val` and verify `matchesKey`
(`d = (((wp, base), (b, q_val)), u_val)`). -/
@[irreducible] private def probeLiveCandGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), (b, q_val)), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let lk ← probeLiveLookupGenProg ((wp, base), (b, u_val))
    if lk.1 = z1 then do
      let ok ← matchesKeyGenProg (((wp.1, base), (b, q_val)), (b, lk.2))
      if ok = z1 then pure (z1, lk.2) else pure (z0, z0)
    else
      pure (z0, z0)

/-- Precondition for `probeLiveCandGenProg`. -/
private def ProbeLiveCandPre (w : ℕ) :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((wp, base), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (mapFn : ℕ → Option ℕ),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      fs.liveRole b < 3 ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeLiveCandGen :
    Realizes .exact probeLiveCandGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeLiveCandPre
      (fun _ _ => 0) := by
  unfold probeLiveCandGenProg
  have hpl := realizes_probeLiveLookupGen
  have hmk := realizes_matchesKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, heq_wp, hseed, hrep,
      hb, hlr, hins, hv_sl, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hlk_st, _, _, _⟩ :=
      probeLiveLookupGenProg_spec (u_val := u_val) henv hseed hrep hb hlr hins hv_sl (s := s)
    simp only [hcp_eq, hlk_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, mapFn, henv, rfl, hseed, hrep, hb, hlr, hins, hv_sl⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩
  )

private theorem probeLiveCandGenProg_spec {c U V w n_max base b q_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (u : Fin U) :
    let prog := probeLiveCandGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let cand : Option ℕ :=
      match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
      | none => none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 272 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hlk_st, hlk_res, hlk_mc, hlk_vp⟩ :=
    probeLiveLookupGenProg_spec (u_val := u.val) henv hseed hrep hb hlr hins hv_sl (s := s)
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu⟩ else 0
     else 0) = fp := by
    dsimp only [fp, fpOfSalt]
    split_ifs with hs hu
    · rfl
    · exact absurd u.isLt hu
    · rfl
  rw [hfp_eq] at hlk_res
  have hlk_mc' : memoryCost (probeLiveLookupGenProg
      ((mkWhpParams c U V w n_max, base), (b, u.val))) s ≤ hashEvalCostWhp c + 266 := hlk_mc
  dsimp only
  unfold probeLiveCandGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp with
  | none =>
    rw [hlk] at hlk_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hlk_st, hlk_res]; rfl
    · rw [clientResult_bind, hlk_st, hlk_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hlk_st, hlk_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hlk_vp ?_; rw [hlk_st, hlk_res]; exact validProg_pure _
  | some loc =>
    rw [hlk] at hlk_res
    obtain ⟨hm_st, hm_res, hm_mc, hm_vp⟩ :=
      matchesKeyGenProg_spec henv hrep hb hcnt_le hbp_v (q_val := q_val) (b_cand := b)
        (loc := loc) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      rw [clientState_bind, hm_st]; split_ifs <;> rfl
    · rw [clientResult_bind, hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      rw [clientResult_bind, hm_st, hm_res]
      cases hmk : fs.matchesKey n_max b q_val b loc <;> simp
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
      rw [hm_st]
      have hm_mc' : memoryCost (matchesKeyGenProg
          (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (b, loc))) s ≤ 6 := hm_mc
      split_ifs <;> (simp only [memoryCost_pure]; omega)
    · refine validProg_bind hlk_vp ?_; rw [hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      refine validProg_bind hm_vp ?_; rw [hm_st]; split_ifs <;> exact validProg_pure _

/-- Shared memory-state precondition for foreground fast-mode operations under `ValidFastState`. -/
@[expose] def ValidFastMemPre (w : ℕ) (wp : WhpParams) (base : ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
    WhpLargeEnv c U V w₀ n_max w base ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    FastMemRep base c U V w₀ n_max fs s.mem ∧
    ValidFastState c U V n_max θ fs dict

/-- Probe `buf oldEp` when `rebStage ≤ 3` (`d = (((cp, base), (b, q_val)), rKey)`). -/
@[irreducible] private def probeOldBufCandGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, base), (b, q_val)), rKey) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let stg ← readHdrProg (base, hdrRebStage)
    if stg ≤ z3 then do
      let oldEp ← readOldEpProg base
      probeBufCandGenProg ((((cp, base), oldEp), (b, q_val)), rKey)
    else
      pure (z0, z0)

private def ProbeOldBufCandPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, base), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (fs.curEp = 0 ∨ fs.curEp = 1) ∧
      (fs.rebStage ≤ 3 → ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap) ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeOldBufCandGen :
    Realizes .exact probeOldBufCandGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeOldBufCandPre
      (fun _ _ => 0) := by
  unfold probeOldBufCandGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hpb := realizes_probeBufCandGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, q_val⟩⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hbo_fn, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hlog_w := henv.log_lt_w
    have hbm_ge := bMinWhp_le_log hth
    have hbmin := le_bMinWhp c
    have hw2 : 2 ≤ w := by omega
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (s := s) (by dsimp [hdrRebStage]; omega)
    rw [hrep.2.2.2.2.2.1] at hst_res
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce_or with h0 | h1
      · simp [FastState.oldEp, h0]
      · simp [FastState.oldEp, h1]
    simp only [hst_st, hst_res] at *
    simp only [hro_st, hro_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hw2
    | (obtain ⟨oldMap, hv_old⟩ := hbo_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs, oldMap, henv, rfl, hrep, hold_or, hv_old,
         hb, hcnt_le, hbp_v⟩)
  )

private theorem probeOldBufCandGenProg_spec {c U V w n_max base b q_val rKey : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := probeOldBufCandGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)
    let cand : Option ℕ :=
      if fs.rebStage ≤ 3 then
        match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
        | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
        | none => none
      else none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (s := s) (by dsimp [hdrRebStage]; omega)
  rw [hrep.2.2.2.2.2.1] at hst_res
  dsimp only
  unfold probeOldBufCandGenProg
  simp only [pure_bind]
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce_or with h0 | h1
      · simp [FastState.oldEp, h0]
      · simp [FastState.oldEp, h1]
    obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    obtain ⟨hp_st, hp_res, hp_mc, hp_vp⟩ :=
      probeBufCandGenProg_spec henv hold_or hrep hv_old hb hcnt_le hbp_v
        (q_val := q_val) (rKey := rKey) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, ite_eq_left hle3,
        clientState_bind, hro_st, hro_res, hp_st]
    · rw [clientResult_bind, hst_st, hst_res, ite_eq_left hle3,
        clientResult_bind, hro_st, hro_res, hp_res, ite_eq_left hle3]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_left hle3, memoryCost_bind, hro_st, hro_res, hro_mc]
      omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_left hle3]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      exact hp_vp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, ite_eq_right hle3]; rfl
    · rw [clientResult_bind, hst_st, hst_res, ite_eq_right hle3, ite_eq_right hle3]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hle3]; simp only [memoryCost_pure]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_right hle3]
      exact validProg_pure _

/-- Inner lookup helper given precomputed `(b, q_val)` (`d = (((wp, base), (b, q_val)), u_val)`). -/
@[irreducible] def fastFindLocBqGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), (b, q_val)), u_val) => do
    let z1 ← pure 1
    let hrt ← mkHashRtGenProg (wp, base)
    let rKey ← fpReducedKeyOptRtProg (hrt, u_val)
    let curEp ← readHdrProg (base, hdrCurEp)
    let c1 ← probeBufCandGenProg ((((wp.1, base), curEp), (b, q_val)), rKey)
    if c1.1 = z1 then
      pure c1
    else do
      let c2 ← probeOldBufCandGenProg (((wp.1, base), (b, q_val)), rKey)
      if c2.1 = z1 then
        pure c2
      else
        probeLiveCandGenProg (((wp, base), (b, q_val)), u_val)

theorem realizes_fastFindLocBqGen :
    Realizes .exact fastFindLocBqGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (((wp, base), (b, _)), _) s =>
        ValidFastMemPre w wp base s ∧ b < wpM wp.1)
      (fun _ _ => 0) := by
  unfold fastFindLocBqGenProg
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_fpReducedKeyOptRt
  have hrh := realizes_readHdr
  have hpb := realizes_probeBufCandGen
  have hpo := realizes_probeOldBufCandGen
  have hpl := realizes_probeLiveCandGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hb_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hb : b < numBucketsWhp n_max := by
      rw [hcp_eq, wp_large_M hth] at hb_wp; exact hb_wp
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hm2 : s.mem (base + hdrCurEp) = fs.curEp := hrep.2.2.2.1
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hrk_st, _, _, _⟩ :=
      fpReducedKeyOptRtProg_spec (kv := u_val) henv hseed (s := s)
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (s := s) (by dsimp [hdrCurEp]; omega)
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hcnt_le := hv.bktCount_le b hb
    have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
      fun k hk => (hv.backPtr_valid b hb k hk).1
    have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      have hbo := hv.bufOld_valid
      rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo
      exact ⟨oldMap, hv_old⟩
    set rk_res := (Memory.spec 0).clientResult s
      (fpReducedKeyOptRtProg (mkHashRt c U w n_max base, u_val))
    obtain ⟨hc1_st, _, _, _⟩ := probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le
      hbp_v (q_val := q_val) (rKey := rk_res) (s := s)
    obtain ⟨hc2_st, _, _, _⟩ := probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn
      hb hcnt_le hbp_v (q_val := q_val) (rKey := rk_res) (s := s)
    dsimp only [rk_res] at hc1_st hc2_st
    simp only [hcp_eq] at *
    simp only [hmh_st, hmh_res] at *
    simp only [hrk_st] at *
    simp only [hce_st, hce_res, hm2] at *
    simp only [hc1_st] at *
    simp only [hc2_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur,
        hb, hcnt_le, hbp_v⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hv.curEp_or, hbo_fn, hb, hcnt_le, hbp_v⟩
    | (obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
       have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
       have hl_role := (hv.roles_valid b hb).1
       exact ⟨c, U, V, w, n_max, θ, fs, liveMap, henv, rfl, hseed, hrep,
         hb, hl_role, hins, hv_live, hcnt_le, hbp_v⟩)
  )

private def evalBufCand (n_max b q_val : ℕ) (fs : FastState) :
    Option (ℕ × ℕ) → Option ℕ
  | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
  | none => none

private theorem fastFindLoc_cases (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let rKey := fpReducedKey c U n_max θ.2 u
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let c1 := evalBufCand n_max b q_val fs
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey)
    let c2 :=
      if fs.rebStage ≤ 3 then
        evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
      else none
    let c3 : Option ℕ :=
      match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
      | none => none
    (∀ loc, c1 = some loc → fastFindLoc c U n_max θ fs u = some loc) ∧
    (∀ loc, c1 = none → c2 = some loc → fastFindLoc c U n_max θ fs u = some loc) ∧
    (c1 = none → c2 = none →
      (match fastFindLoc c U n_max θ fs u with | some loc => (1, loc) | none => (0, 0)) =
      (match c3 with | some loc => (1, loc) | none => (0, 0))) := by
  dsimp only [fastFindLoc, evalBufCand]
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  set rKey := fpReducedKey c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
  | none =>
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
    | none =>
      cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | none => split_ifs <;> simp
      | some l3 =>
        dsimp only
        rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
          (rw [h3]; split_ifs <;> simp)
    | some p2 =>
      rcases p2 with ⟨b2, l2⟩; dsimp only
      rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b2 l2) with h2 | h2 <;>
        (rw [h2];
         cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
           (fs.slices (fs.liveSliceIdx b)) fp with
         | none => split_ifs <;> simp
         | some l3 =>
           dsimp only
           rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
             (rw [h3]; split_ifs <;> simp))
  | some p1 =>
    rcases p1 with ⟨b1, l1⟩; dsimp only
    rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b1 l1) with h1 | h1 <;>
      (rw [h1];
       cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
       | none =>
         cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
             (fs.slices (fs.liveSliceIdx b)) fp with
         | none => split_ifs <;> simp
         | some l3 =>
           dsimp only
           rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
             (rw [h3]; split_ifs <;> simp)
       | some p2 =>
         rcases p2 with ⟨b2, l2⟩; dsimp only
         rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b2 l2) with h2 | h2 <;>
           (rw [h2];
            cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices (fs.liveSliceIdx b)) fp with
            | none => split_ifs <;> simp
            | some l3 =>
              dsimp only
              rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
                (rw [h3]; split_ifs <;> simp)))

theorem fastFindLocBqGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let prog := fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match fastFindLoc c U n_max θ fs u with
       | some loc => (1, loc)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + hashEvalCostWhp c + 304 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro b q_val
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hcnt_le := hv.bktCount_le b hb
  have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
    fun k hk => (hv.backPtr_valid b hb k hk).1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  set rKey := fpReducedKey c U n_max θ.2 u
  have hrk_eq : (if h : u.val < U then fpReducedKey c U n_max θ.2 ⟨u.val, h⟩ else 0) = rKey := by
    simp [rKey, u.isLt]
  rw [hrk_eq] at hrk_res
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (s := s) (by dsimp [hdrCurEp]; omega)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
  obtain ⟨hc1_st, hc1_res, hc1_mc, hc1_vp⟩ :=
    probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le hbp_v
      (q_val := q_val) (rKey := rKey) (s := s)
  have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
    intro hle3
    have hbo := hv.bufOld_valid
    rw [ite_eq_left hle3] at hbo
    obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo
    exact ⟨oldMap, hv_old⟩
  obtain ⟨hc2_st, hc2_res, hc2_mc, hc2_vp⟩ :=
    probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn hb hcnt_le hbp_v
      (q_val := q_val) (rKey := rKey) (s := s)
  obtain ⟨hfl_c1, hfl_c2, hfl_c3⟩ := fastFindLoc_cases c U n_max θ fs u
  have hc1_res_ev : (Memory.spec 0).clientResult s
      (probeBufCandGenProg
        ((((mkWhpCoreParams c U V w n_max, base), fs.curEp), (b, q_val)), rKey)) =
      (match evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) with
       | some loc => (1, loc) | none => (0, 0)) := by
    rw [hc1_res]
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey <;> rfl
  have hc2_res_ev : (Memory.spec 0).clientResult s
      (probeOldBufCandGenProg
        (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)) =
      (match (if fs.rebStage ≤ 3 then
          evalBufCand n_max b q_val fs
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
        else none) with
       | some loc => (1, loc) | none => (0, 0)) := by
    rw [hc2_res]
    by_cases hs3 : fs.rebStage ≤ 3
    · rw [ite_eq_left hs3, ite_eq_left hs3]
      cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey <;> rfl
    · rw [ite_eq_right hs3, ite_eq_right hs3]
  have hmh_mc' : memoryCost (mkHashRtGenProg (mkWhpParams c U V w n_max, base)) s = 0 := hmh_mc
  have hrk_mc' : memoryCost (fpReducedKeyOptRtProg (mkHashRt c U w n_max base, u.val)) s ≤ 1 :=
    hrk_mc
  have hc1_mc' : memoryCost (probeBufCandGenProg
      ((((mkWhpCoreParams c U V w n_max, base), fs.curEp), (b, q_val)), rKey)) s ≤
      2 * cTabWhp c + 14 := hc1_mc
  have hc2_mc' : memoryCost (probeOldBufCandGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)) s ≤
      2 * cTabWhp c + 16 := hc2_mc
  dsimp only
  unfold fastFindLocBqGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  cases hc1 : evalBufCand n_max b q_val fs
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) with
  | some loc1 =>
    rw [hfl_c1 loc1 hc1]
    rw [hc1] at hc1_res_ev
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
        clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
      rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
        clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
      rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
      refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
      exact validProg_pure _
  | none =>
    rw [hc1] at hc1_res_ev
    cases hc2 : (if fs.rebStage ≤ 3 then
        evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
      else none) with
    | some loc2 =>
      rw [hfl_c2 loc2 hc1 hc2]
      rw [hc2] at hc2_res_ev
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
          clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientState_bind, hc2_st, hc2_res_ev]; rfl
      · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
          clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientResult_bind, hc2_st, hc2_res_ev]; rfl
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
        rw [hc2_st, hc2_res_ev]; simp only [↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
        refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
        refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
        refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        refine validProg_bind hc2_vp ?_; rw [hc2_st, hc2_res_ev]
        exact validProg_pure _
    | none =>
      rw [hc2] at hc2_res_ev
      obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
      have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
      obtain ⟨hpl_st, hpl_res, hpl_mc, hpl_vp⟩ :=
        probeLiveCandGenProg_spec henv hseed hrep hb (hv.roles_valid b hb).1 hins hv_live
          hcnt_le hbp_v u (q_val := q_val) (s := s)
      have hpl_mc' : memoryCost (probeLiveCandGenProg
          (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)) s ≤
          hashEvalCostWhp c + 272 := hpl_mc
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
          clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientState_bind, hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_st
      · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
          clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientResult_bind, hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_res.trans (hfl_c3 hc1 hc2).symm
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
        rw [hc2_st, hc2_res_ev]; simp only [zero_ne_one, ↓reduceIte]; omega
      · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
        refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
        refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
        refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        refine validProg_bind hc2_vp ?_; rw [hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_vp

/-- Fast-mode value query `fastQueryGenProg` (`d = ((wp, base), u_val)`), returning `(1, val)` or
`(0, 0)` in `O_c(1)` worst-case memory operations without mutating memory. -/
@[irreducible] def fastQueryGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((wp, base), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then do
      let p ← physSlotGenProg (((wp.1, base), bq.1), fl.2)
      let val ← readValGenProg ((wp.1, base), p)
      pure (z1, val)
    else
      pure (z0, z0)

theorem realizes_fastQueryGen :
    Realizes .exact fastQueryGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), u_val) s => ValidFastMemPre w wp base s ∧ u_val < wpU wp.1)
      (fun _ _ => 0) := by
  unfold fastQueryGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hfl := realizes_fastFindLocBqGen
  have hps := realizes_physSlotGen
  have hrv := realizes_readValGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    obtain ⟨hfl_st, hfl_res, _, _⟩ :=
      fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    simp only [hcp_eq] at *
    simp only [hmh_st, hmh_res, hfs_st, hfs_res, hfl_st, wp_large_M hth, wp_large_nMax hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none =>
         have hhit : ((Memory.spec 0).clientResult s
           (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base),
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
              keyQuotient (bWhp n_max) u_val)), u_val))).1 = 1 := by assumption
         rw [hfind] at hfl_res; rw [hfl_res] at hhit; cases hhit
       | some loc =>
         rw [hfind] at hfl_res hspec
         rw [hfl_res]
         have hloc_b : loc < fs.bktCount
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val) := hspec.1
         have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le _ hb)
         have hbp : capFrontWhp n_max ≤ loc →
             fs.backPtr (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val)
               (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
           fun hcf => (hv.backPtr_valid _ hb _ (by omega)).1
         first
         | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
         | (obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ :=
              physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
            simp only [hps_st, hps_res] at *
            exact hps_lt))
  )

theorem fastQueryGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let prog := fastQueryGenProg ((mkWhpParams c U V w n_max, base), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match fastQuery c U n_max θ fs u with
       | some v => (1, v)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + 2 * hashEvalCostWhp c + 308 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  unfold fastQueryGenProg fastQuery
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res,
        clientState_bind, hfl_st, hfl_res]; rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res,
        clientResult_bind, hfl_st, hfl_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res, hfl_st, hfl_res]
      simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]
      refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
      exact validProg_pure _
  | some loc =>
    rw [hfind] at hfl_res hspec
    have hloc_b : loc < fs.bktCount b := hspec.1
    have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
    have hbp : capFrontWhp n_max ≤ loc →
        fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
    obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
      physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    obtain ⟨hrv_st, hrv_res, hrv_mc, hrv_vp⟩ := readValGenProg_spec henv hps_lt hrep (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res,
        clientState_bind, hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientState_bind, hps_st, hps_res, clientState_bind, hrv_st]; rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res,
        clientResult_bind, hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientResult_bind, hps_st, hps_res, clientResult_bind, hrv_st, hrv_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res, hfl_st, hfl_res]
      dsimp only; simp only [↓reduceIte, memoryCost_bind]
      rw [hps_st, hps_res, hrv_st, hrv_mc]
      have hmh_mc' : memoryCost (mkHashRtGenProg (mkWhpParams c U V w n_max, base)) s = 0 := hmh_mc
      have hfs_mc' : memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s ≤
          hashEvalCostWhp c := hfs_mc
      have hfl_mc' : memoryCost (fastFindLocBqGenProg
          (((mkWhpParams c U V w n_max, base),
            (b, keyQuotient (bWhp n_max) u.val)), u.val)) s ≤
          4 * cTabWhp c + hashEvalCostWhp c + 304 := hfl_mc
      have hps_mc' : memoryCost (physSlotGenProg
          (((mkWhpCoreParams c U V w n_max, base), b), loc)) s ≤ 2 := hps_mc
      have hrv_mc' : memoryCost (readValGenProg
          ((mkWhpCoreParams c U V w n_max, base), fs.physSlot n_max b loc)) s = 2 := hrv_mc
      dsimp only [b] at hfl_mc' hps_mc' hrv_mc' ⊢
      simp only [memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]
      refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
      dsimp only; simp only [↓reduceIte]
      refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]
      refine validProg_bind hrv_vp ?_; rw [hrv_st]
      exact validProg_pure _

/-! ## Section 5: Per-Bucket Overmars Rebuild (`overmarsStepGenProg`) -/

/-- Compact 4-word runtime descriptor `((base, offBktMeta), (globalPtrBits, w))` for `bktMeta`
packed-array accesses, keeping `realize` elaboration independent of `WhpCoreParams` width. -/
abbrev BktMetaRt : Type := (ℕ × ℕ) × (ℕ × ℕ)

/-- Construct the 4-word `BktMetaRt` descriptor for `(c, U, V, w, n_max, base)`. -/
@[expose] def mkBktMetaRt (c U V w n_max base : ℕ) : BktMetaRt :=
  ((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w))

/-- Project `BktMetaRt` from `(cp, base)` in zero memory steps. -/
@[irreducible] def mkBktMetaRtProg : WhpCoreParams × ℕ → Memory.Prog BktMetaRt
  | (cp, base) => do
    let off ← pure (wpOffBktMeta cp)
    let g ← pure (wpGlobalPtrBits cp)
    let ww ← pure (wpW cp)
    pure ((base, off), (g, ww))

theorem realizes_mkBktMetaRt :
    Realizes .exact mkBktMetaRtProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := BktMetaRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkBktMetaRtProg
  realize

theorem mkBktMetaRtProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkBktMetaRtProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkBktMetaRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkBktMetaRtProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  exact ⟨rfl, rfl, rfl, validProg_pure _⟩

/-- Existential admissibility predicate for `(bm, b)` on `bktMeta`. -/
@[expose] def BktMetaBucketEnv (w : ℕ) (bm : BktMetaRt) (b : ℕ) : Prop :=
  ∃ c U V w₀ n_max base,
    WhpLargeEnv c U V w₀ n_max w base ∧
    bm = mkBktMetaRt c U V w₀ n_max base ∧
    b < numBucketsWhp n_max

/-- Set `(overmarsActive b, overmarsCursor b, overmarsInsCount b) := (actVal, 0, 0)` on `BktMetaRt`
(`d = ((bm, b), actVal)`). -/
@[irreducible] def setOvermarsActRtProg : (BktMetaRt × ℕ) × ℕ → Memory.Prog Unit
  | ((bm, b), actVal) => do
    let z0 ← pure 0
    let i5 ← pure (16 * b + 5)
    let i6 ← pure (16 * b + 6)
    let i7 ← pure (16 * b + 7)
    writePackedGenProg ((bm, i5), actVal)
    writePackedGenProg ((bm, i6), z0)
    writePackedGenProg ((bm, i7), z0)

theorem realizes_setOvermarsActRt :
    Realizes .exact setOvermarsActRtProg
      (WordEncoding.encode (α := (BktMetaRt × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((bm, b), _) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold setOvermarsActRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨bm, b⟩, actVal⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

theorem setOvermarsActRtProg_fastStep {c U V w n_max base b actVal : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hact_le : actVal ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := setOvermarsActRtProg ((mkBktMetaRt c U V w n_max base, b), actVal)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        overmarsActive := Function.update fs.overmarsActive b actVal
        overmarsCursor := Function.update fs.overmarsCursor b 0
        overmarsInsCount := Function.update fs.overmarsInsCount b 0 } s s' := by
  have hth := henv.2.2.2.1
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 5 < 10) hact_le hseed hrep (s := s)
  set cp := mkWhpCoreParams c U V w n_max
  set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 5), actVal))
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10) (Nat.zero_le n_max)
      hw1_step.2.1 hw1_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeBktFieldGenProg ((((cp, base), b), 6), 0))
  obtain ⟨hw3_mc, hw3_vp, hw3_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10) (Nat.zero_le n_max)
      hw2_step.2.1 hw2_step.2.2.1 (s := s2)
  have hw_eq : ∀ f v,
      writePackedGenProg (((mkBktMetaRt c U V w n_max base, 16 * b + f), v)) =
      writeBktFieldGenProg ((((cp, base), b), f), v) := by
    intro f v
    unfold writeBktFieldGenProg
    simp only [cp, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      pure_bind, mkBktMetaRt]
  unfold setOvermarsActRtProg
  simp only [pure_bind, hw_eq]
  have hs'_eq : (Memory.spec 0).clientState s
      (writeBktFieldGenProg ((((cp, base), b), 5), actVal) >>= fun _ =>
        writeBktFieldGenProg ((((cp, base), b), 6), 0) >>= fun _ =>
        writeBktFieldGenProg ((((cp, base), b), 7), 0)) =
      (Memory.spec 0).clientState s2 (writeBktFieldGenProg ((((cp, base), b), 7), 0)) := by
    rw [clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, validProg_bind hw1_vp (validProg_bind hw2_vp hw3_vp),
    (hw1_step.trans hw2_step).trans hw3_step⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1, s2, cp] at hw1_mc hw2_mc hw3_mc ⊢
  omega

/-- Swap `liveRole b` and `overmarsRole b` and set `liveInsCount b := overmarsInsCount b` on
`BktMetaRt` (`d = (bm, b)`). -/
@[irreducible] private def overmarsSwapRolesRtProg : BktMetaRt × ℕ → Memory.Prog Unit
  | (bm, b) => do
    let i2 ← pure (16 * b + 2)
    let i3 ← pure (16 * b + 3)
    let i4 ← pure (16 * b + 4)
    let i7 ← pure (16 * b + 7)
    let oldLive ← readPackedGenProg (bm, i2)
    let oldOm ← readPackedGenProg (bm, i4)
    let omIns ← readPackedGenProg (bm, i7)
    writePackedGenProg ((bm, i2), oldOm)
    writePackedGenProg ((bm, i4), oldLive)
    writePackedGenProg ((bm, i3), omIns)

private theorem realizes_overmarsSwapRolesRt :
    Realizes .exact overmarsSwapRolesRtProg
      (WordEncoding.encode (α := BktMetaRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (bm, b) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold overmarsSwapRolesRtProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨bm, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

private theorem overmarsSwapRolesRtProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs.liveRole b ≤ n_max) (hor : fs.overmarsRole b ≤ n_max)
    (hins : fs.overmarsInsCount b ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsSwapRolesRtProg (mkBktMetaRt c U V w n_max base, b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        liveRole := Function.update fs.liveRole b (fs.overmarsRole b)
        overmarsRole := Function.update fs.overmarsRole b (fs.liveRole b)
        liveInsCount := Function.update fs.liveInsCount b (fs.overmarsInsCount b) } s s' := by
  have hth := henv.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  have hr_eq : ∀ f,
      readPackedGenProg (mkBktMetaRt c U V w n_max base, 16 * b + f) =
      readBktFieldGenProg (((cp, base), b), f) := by
    intro f
    unfold readBktFieldGenProg
    simp only [cp, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      pure_bind, mkBktMetaRt]
  have hw_eq : ∀ f v,
      writePackedGenProg ((mkBktMetaRt c U V w n_max base, 16 * b + f), v) =
      writeBktFieldGenProg ((((cp, base), b), f), v) := by
    intro f v
    unfold writeBktFieldGenProg
    simp only [cp, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      pure_bind, mkBktMetaRt]
  obtain ⟨h2_st, h2_res, h2_mc, h2_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s)
  obtain ⟨h4_st, h4_res, h4_mc, h4_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
  obtain ⟨h7_st, h7_res, h7_mc, h7_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep (s := s)
  simp only [getBktField] at h2_res h4_res h7_res
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 2 < 10) hor hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (writeBktFieldGenProg ((((cp, base), b), 2), fs.overmarsRole b))
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 4 < 10) hlr
      hw1_step.2.1 hw1_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1
    (writeBktFieldGenProg ((((cp, base), b), 4), fs.liveRole b))
  obtain ⟨hw3_mc, hw3_vp, hw3_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 3 < 10) hins
      hw2_step.2.1 hw2_step.2.2.1 (s := s2)
  unfold overmarsSwapRolesRtProg
  simp only [pure_bind, hr_eq, hw_eq]
  have hs'_eq : (Memory.spec 0).clientState s
      (readBktFieldGenProg (((cp, base), b), 2) >>= fun oldLive =>
        readBktFieldGenProg (((cp, base), b), 4) >>= fun oldOm =>
        readBktFieldGenProg (((cp, base), b), 7) >>= fun omIns =>
        writeBktFieldGenProg ((((cp, base), b), 2), oldOm) >>= fun _ =>
        writeBktFieldGenProg ((((cp, base), b), 4), oldLive) >>= fun _ =>
        writeBktFieldGenProg ((((cp, base), b), 3), omIns)) =
      (Memory.spec 0).clientState s2
        (writeBktFieldGenProg ((((cp, base), b), 3), fs.overmarsInsCount b)) := by
    rw [clientState_bind, h2_st, h2_res, clientState_bind, h4_st, h4_res,
      clientState_bind, h7_st, h7_res, clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hw1_step.trans hw2_step).trans hw3_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h2_st, h2_res, h2_mc, h4_st, h4_res, h4_mc, h7_st, h7_res, h7_mc]
    dsimp only [s1, s2, cp] at hw1_mc hw2_mc hw3_mc ⊢
    omega
  · refine validProg_bind h2_vp ?_; rw [h2_st, h2_res]
    refine validProg_bind h4_vp ?_; rw [h4_st, h4_res]
    refine validProg_bind h7_vp ?_; rw [h7_st, h7_res]
    exact validProg_bind hw1_vp (validProg_bind hw2_vp hw3_vp)

/-- Inner activation action of `overmarsStep` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsDoActivateGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z1 ← pure 1
    let omRole ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + omRole)
    let bm ← mkBktMetaRtProg (cp, base)
    setOvermarsActRtProg ((bm, b), z1)
    resetBTreeSliceGenProg ((cp, base), omIdx)

private theorem realizes_overmarsDoActivateGen :
    Realizes .exact overmarsDoActivateGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsDoActivateGenProg
  have hrb := realizes_readBktFieldGen
  have hmb := realizes_mkBktMetaRt
  have hsa := realizes_setOvermarsActRt
  have hrs := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨h4_st, h4_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
    simp only [getBktField] at h4_res
    obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [h4_st, h4_res] at *
    simp only [hmb_st, hmb_res] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | trivial
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩
    | omega
  )

/-- Activation substep of `overmarsStep` on bucket `b` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsActivateGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let act ← readBktFieldGenProg (((cp, base), b), 5)
    let lic ← readBktFieldGenProg (((cp, base), b), 3)
    if act = z0 ∧ wpOvermarsThresh cp ≤ lic then
      overmarsDoActivateGenProg ((cp, base), b)
    else
      pure ()

private theorem realizes_overmarsActivateGen :
    Realizes .exact overmarsActivateGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsActivateGenProg
  have hrb := realizes_readBktFieldGen
  have hda := realizes_overmarsDoActivateGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨h5_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep (s := s)
    obtain ⟨h3_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
    simp only [h5_st] at *
    simp only [h3_st] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
  )

private theorem overmarsActivateGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsActivateGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let fs0 : FastState :=
      if fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b then
        let omIdx := fs.overmarsSliceIdx b
        { fs with
          overmarsActive := Function.update fs.overmarsActive b 1
          overmarsCursor := Function.update fs.overmarsCursor b 0
          overmarsInsCount := Function.update fs.overmarsInsCount b 0
          slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx)) }
      else fs
    memoryCost prog s ≤ 26 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs0 s s' := by
  have hth := henv.2.2.2.1
  have hn1 : 1 ≤ n_max := by have := four_le_of_whpThreshold_le hth; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨h5_st, h5_res, h5_mc, h5_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep (s := s)
  obtain ⟨h3_st, h3_res, h3_mc, h3_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
  simp only [getBktField] at h5_res h3_res
  dsimp only
  unfold overmarsActivateGenProg
  simp only [cp, wp_large_overmarsThresh hth, pure_bind]
  by_cases htrig : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
  · rw [ite_eq_left htrig]
    obtain ⟨h4_st, h4_res, h4_mc, h4_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
    simp only [getBktField] at h4_res
    obtain ⟨hmb_st, hmb_res, hmb_mc, hmb_vp⟩ :=
      mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base)
        hth s
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hsa_mc, hsa_vp, hsa_step⟩ :=
      setOvermarsActRtProg_fastStep henv hb hn1 hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s
      (setOvermarsActRtProg ((mkBktMetaRt c U V w n_max base, b), 1))
    obtain ⟨hrs_mc, hrs_vp, hrs_step⟩ :=
      resetBTreeSliceGenProg_fastStep henv homIdx hsa_step.2.1 hsa_step.2.2.1 (s := s1)
    have homIdx_def : 3 * b + fs.overmarsRole b = fs.overmarsSliceIdx b := rfl
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 5) >>= fun act =>
          readBktFieldGenProg (((cp, base), b), 3) >>= fun lic =>
          if act = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ lic then
            overmarsDoActivateGenProg ((cp, base), b)
          else pure ()) =
        (Memory.spec 0).clientState s1
          (resetBTreeSliceGenProg ((cp, base), fs.overmarsSliceIdx b)) := by
      rw [clientState_bind, h5_st, h5_res, clientState_bind, h3_st, h3_res,
        ite_eq_left htrig]
      unfold overmarsDoActivateGenProg
      simp only [pure_bind]
      rw [clientState_bind, h4_st, h4_res, homIdx_def,
        clientState_bind, hmb_st, hmb_res, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, hsa_step.trans hrs_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h5_st, h5_res, h5_mc, h3_st, h3_res, h3_mc, ite_eq_left htrig]
      unfold overmarsDoActivateGenProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h4_st, h4_res, h4_mc, homIdx_def, hmb_st, hmb_res, hmb_mc]
      dsimp only [s1, cp] at hsa_mc hrs_mc ⊢
      omega
    · refine validProg_bind h5_vp ?_; rw [h5_st, h5_res]
      refine validProg_bind h3_vp ?_; rw [h3_st, h3_res, ite_eq_left htrig]
      unfold overmarsDoActivateGenProg; simp only [pure_bind]
      refine validProg_bind h4_vp ?_; rw [h4_st, h4_res, homIdx_def]
      refine validProg_bind hmb_vp ?_; rw [hmb_st, hmb_res]
      exact validProg_bind hsa_vp hrs_vp
  · rw [ite_eq_right htrig]
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 5) >>= fun act =>
          readBktFieldGenProg (((cp, base), b), 3) >>= fun lic =>
          if act = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ lic then
            overmarsDoActivateGenProg ((cp, base), b)
          else pure ()) = s := by
      rw [clientState_bind, h5_st, h5_res, clientState_bind, h3_st, h3_res,
        ite_eq_right htrig]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h5_st, h5_res, h5_mc, h3_st, h3_res, h3_mc, ite_eq_right htrig]
      simp only [memoryCost_pure]; omega
    · refine validProg_bind h5_vp ?_; rw [h5_st, h5_res]
      refine validProg_bind h3_vp ?_; rw [h3_st, h3_res, ite_eq_right htrig]
      exact validProg_pure _

/-- Evaluate `inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc)`
(`d = (((cp, base), b), loc)`), returning `1` or `0` without mutating memory. -/
@[irreducible] private def checkCoordInLiveGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) => do
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let st ← readFastLocGenProg (((cp, base), b), loc)
    inLiveTreeProg ((stg, oldEp), (doneB, st))

private theorem realizes_checkCoordInLiveGen :
    Realizes .exact checkCoordInLiveGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), loc) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          loc < totalLocalCoordsWhp n_max)
      (fun _ _ => 0) := by
  unfold checkCoordInLiveGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hrl := realizes_readFastLocGen
  have hil := realizes_inLiveTree
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hb, hloc⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hlog_w := henv.log_lt_w
    have hbm_ge := bMinWhp_le_log hth
    have hbmin := le_bMinWhp c
    have hw2 : 2 ≤ w := by omega
    obtain ⟨hst_st, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (s := s) (by dsimp [hdrRebStage]; omega)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    obtain ⟨hd8_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 8 < 10) hrep (s := s)
    obtain ⟨hlc_st, _, _, _⟩ := readFastLocGenProg_spec henv hb hloc hrep (s := s)
    have hold_le1 : fs.oldEp ≤ 1 := by
      rcases hce_or with h0 | h1
      · simp [FastState.oldEp, h0]
      · simp [FastState.oldEp, h1]
    simp only [hst_st] at *
    simp only [hro_st, hro_res] at *
    simp only [hd8_st] at *
    simp only [hlc_st] at *
    try simp only [wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hw2
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hloc
    | exact hold_le1
  )

private theorem checkCoordInLiveGenProg_spec {c U V w n_max base b loc : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := checkCoordInLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) then 1 else 0) ∧
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (s := s) (by dsimp [hdrRebStage]; omega)
  rw [hrep.2.2.2.2.2.1] at hst_res
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max)
    (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
  obtain ⟨hd8_st, hd8_res, hd8_mc, hd8_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 8 < 10) hrep (s := s)
  simp only [getBktField] at hd8_res
  obtain ⟨hlc_st, hlc_res, hlc_mc, hlc_vp⟩ := readFastLocGenProg_spec henv hb hloc hrep (s := s)
  obtain ⟨hil_st, hil_res, hil_mc, hil_vp⟩ := inLiveTreeProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (rebStage := fs.rebStage) (oldEp := fs.oldEp)
    (rebDoneB := fs.rebDoneFlag b) (st := fs.locState b loc) (s := s)
  dsimp only
  unfold checkCoordInLiveGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hst_st, hst_res, clientState_bind, hro_st, hro_res,
      clientState_bind, hd8_st, hd8_res, clientState_bind, hlc_st, hlc_res, hil_st]
  · rw [clientResult_bind, hst_st, hst_res, clientResult_bind, hro_st, hro_res,
      clientResult_bind, hd8_st, hd8_res, clientResult_bind, hlc_st, hlc_res, hil_res]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_st, hst_res, hst_mc, hro_st, hro_res, hro_mc, hd8_st, hd8_res, hd8_mc,
      hlc_st, hlc_res, hlc_mc, hil_mc]
  · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res]
    refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
    refine validProg_bind hd8_vp ?_; rw [hd8_st, hd8_res]
    refine validProg_bind hlc_vp ?_; rw [hlc_st, hlc_res]
    exact hil_vp

/-- Read `(bktSalt b, (3 * b + overmarsRole b, overmarsInsCount b))` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsReadScanInfoGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((cp, base), b) => do
    let f1 ← pure 1
    let f4 ← pure 4
    let f7 ← pure 7
    let salt ← readBktFieldGenProg (((cp, base), b), f1)
    let omRole ← readBktFieldGenProg (((cp, base), b), f4)
    let omIns ← readBktFieldGenProg (((cp, base), b), f7)
    let omIdx ← pure (3 * b + omRole)
    pure (salt, (omIdx, omIns))

private theorem realizes_overmarsReadScanInfoGen :
    Realizes .exact overmarsReadScanInfoGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsReadScanInfoGenProg
  have hrb := realizes_readBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨h1_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
    obtain ⟨h4_st, h4_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
    obtain ⟨h7_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep (s := s)
    simp only [getBktField] at h4_res
    simp only [h1_st, h4_st, h4_res, h7_st, wp_large_M hth] at *
    first
    | decide
    | assumption
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

private theorem overmarsReadScanInfoGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsReadScanInfoGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.bktSalt b, (fs.overmarsSliceIdx b, fs.overmarsInsCount b)) ∧
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨h1_st, h1_res, h1_mc, h1_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
  obtain ⟨h4_st, h4_res, h4_mc, h4_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
  obtain ⟨h7_st, h7_res, h7_mc, h7_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep (s := s)
  simp only [getBktField] at h1_res h4_res h7_res
  unfold overmarsReadScanInfoGenProg
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, h1_st, clientState_bind, h4_st, clientState_bind, h7_st]; rfl
  · rw [clientResult_bind, h1_st, h1_res, clientResult_bind, h4_st, h4_res,
      clientResult_bind, h7_st, h7_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h1_st, h1_mc, h4_st, h4_mc, h7_st, h7_mc]; rfl
  · refine validProg_bind h1_vp ?_; rw [h1_st]
    refine validProg_bind h4_vp ?_; rw [h4_st]
    refine validProg_bind h7_vp ?_; rw [h7_st]
    exact validProg_pure _

/-- Write `(overmarsCursor b, overmarsInsCount b) := (cur1, omIns1)` via `BktMetaRt`. -/
@[irreducible] private def overmarsWriteCurInsRtProg :
    ((BktMetaRt × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((bm, b), cur1), omIns1) => do
    let i6 ← pure (16 * b + 6)
    let i7 ← pure (16 * b + 7)
    writePackedGenProg ((bm, i6), cur1)
    writePackedGenProg ((bm, i7), omIns1)

private theorem realizes_overmarsWriteCurInsRt :
    Realizes .exact overmarsWriteCurInsRtProg
      (WordEncoding.encode (α := ((BktMetaRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((bm, b), _), _) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold overmarsWriteCurInsRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨bm, b⟩, cur1⟩, omIns1⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

private theorem overmarsWriteCurInsRtProg_fastStep {c U V w n_max base b cur1 omIns1 : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hcur_le : cur1 ≤ n_max) (hins_le : omIns1 ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsWriteCurInsRtProg (((mkBktMetaRt c U V w n_max base, b), cur1), omIns1)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        overmarsCursor := Function.update fs.overmarsCursor b cur1
        overmarsInsCount := Function.update fs.overmarsInsCount b omIns1 } s s' := by
  have hth := henv.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10) hcur_le hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 6), cur1))
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10) hins_le
      hw1_step.2.1 hw1_step.2.2.1 (s := s1)
  have hw_eq : ∀ f v,
      writePackedGenProg ((mkBktMetaRt c U V w n_max base, 16 * b + f), v) =
      writeBktFieldGenProg ((((cp, base), b), f), v) := by
    intro f v
    unfold writeBktFieldGenProg
    simp only [cp, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      pure_bind, mkBktMetaRt]
  unfold overmarsWriteCurInsRtProg
  simp only [pure_bind, hw_eq]
  rw [clientState_bind]
  refine ⟨?_, validProg_bind hw1_vp hw2_vp, hw1_step.trans hw2_step⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1, cp] at hw1_mc hw2_mc ⊢
  omega

/-- Precondition for one Overmars scan step (`p = (((wp, base), b), ())`). -/
private def OvermarsScanOnePre (w : ℕ) (p : ((WhpParams × ℕ) × ℕ) × Unit)
    (s : Memory.State) : Prop :=
  let ((wp, base), b) := p.1
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (omMap : ℕ → Option ℕ),
    WhpLargeEnv c U V w₀ n_max w base ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    FastMemRep base c U V w₀ n_max fs s.mem ∧
    b < numBucketsWhp n_max ∧
    (fs.curEp = 0 ∨ fs.curEp = 1) ∧
    fs.overmarsRole b < 3 ∧
    fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
    fs.overmarsCursor b < n_max ∧
    fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
    (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
    (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
    ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap

/-- Insert `(fpAt salt b cur, cur)` into `overmarsSlice` and advance
`(overmarsCursor, overmarsInsCount)`. -/
@[irreducible] private def overmarsInsertCoordGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let info ← overmarsReadScanInfoGenProg ((wp.1, base), b)
    let fp ← fpAtGenProg ((((wp, base), info.1), b), cur)
    btreeInsertGenProg ((((wp.1, base), info.2.1), fp), cur)
    let bm ← mkBktMetaRtProg (wp.1, base)
    let cur1 ← pure (cur + 1)
    let omIns1 ← pure (info.2.2 + 1)
    overmarsWriteCurInsRtProg (((bm, b), cur1), omIns1)

private theorem realizes_overmarsInsertCoordGen :
    Realizes .exact overmarsInsertCoordGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        OvermarsScanOnePre w (((wp, base), b), ()) s ∧
        cur = readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 6) ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 0))
      (fun _ _ => 0) := by
  unfold overmarsInsertCoordGenProg
  have hri := realizes_overmarsReadScanInfoGen
  have hfp := realizes_fpAtGen
  have hbi := realizes_btreeInsertGen
  have hmb := realizes_mkBktMetaRt
  have hwc := realizes_overmarsWriteCurInsRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, heq_wp, hseed, hrep, hb, _, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩, hcur_eq0, hcur_lt0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rw [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth]
      at hcur_eq0 hcur_lt0
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    rw [hbm.2.2.2.2.2.2.1] at hcur_eq0
    rw [hbm.1] at hcur_lt0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
      have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
      rw [two_pow_valLaneBitsWhp]; omega
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have hM_ge := (large_bounds_lt_n_max hth).1
    have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by omega : 8 ≤ numBucketsWhp n_max)).trans hML12
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hri_st, hri_res, _, _⟩ := overmarsReadScanInfoGenProg_spec henv hb hrep (s := s)
    have hbp_cur : capFrontWhp n_max ≤ cur → fs.backPtr b (cur - capFrontWhp n_max) <
        poolSizeWhp n_max := fun hcf => hbp_v _ (by omega)
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpAtGenProg_spec henv hseed hrep hb hcur_tot hbp_cur (salt := fs.bktSalt b) (s := s)
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hbi_mc, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om
        (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val (s := s)
    obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth
      ((Memory.spec 0).clientState s
        (btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), fs.overmarsSliceIdx b),
          fs.fpAt c U n_max θ (fs.bktSalt b) b cur), cur)))
    simp only [hcp_eq] at *
    simp only [hri_st, hri_res] at *
    simp only [hfp_st, hfp_res] at *
    simp only [hmb_st, hmb_res] at *
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hcur_tot, hbp_cur⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), omMap,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om,
        fpAt_lt θ fs (fs.bktSalt b) b cur, hcur_val⟩
    | exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩
  )

/-- Increment `overmarsCursor b` to `cur + 1` (`d = (((cp, base), b), cur)`). -/
@[irreducible] private def overmarsIncCurGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), cur) => do
    let f6 ← pure 6
    let cur1 ← pure (cur + 1)
    writeBktFieldGenProg ((((cp, base), b), f6), cur1)

private theorem realizes_overmarsIncCurGen :
    Realizes .exact overmarsIncCurGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), cur) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ cur < wpNMax cp)
      (fun _ _ => 0) := by
  unfold overmarsIncCurGenProg
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, cur⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hcur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    rw [wp_large_nMax hth] at hcur
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

/-- Read `(overmarsCursor b, bktCount b)` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsReadCurCntGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let f6 ← pure 6
    let f0 ← pure 0
    let cur ← readBktFieldGenProg (((cp, base), b), f6)
    let cnt ← readBktFieldGenProg (((cp, base), b), f0)
    pure (cur, cnt)

private theorem realizes_overmarsReadCurCntGen :
    Realizes .exact overmarsReadCurCntGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsReadCurCntGenProg
  have hrb := realizes_readBktFieldGen
  have hcs_r : ∀ x (s' : Memory.State),
      (Memory.spec 0).clientState s' (readBktFieldGenProg x) = s' := by
    rintro ⟨⟨⟨_, _⟩, _⟩, _⟩ _; unfold readBktFieldGenProg; simp only [pure_bind]; rfl
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    simp only [hcs_r, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem overmarsReadCurCntGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsReadCurCntGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (fs.overmarsCursor b, fs.bktCount b) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨h6_st, h6_res, h6_mc, h6_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 6 < 10) hrep (s := s)
  obtain ⟨h0_st, h0_res, h0_mc, h0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at h6_res h0_res
  unfold overmarsReadCurCntGenProg
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, h6_st, clientState_bind, h0_st]; rfl
  · rw [clientResult_bind, h6_st, h6_res, clientResult_bind, h0_st, h0_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h6_st, h6_mc, h0_st, h0_mc]; rfl
  · refine validProg_bind h6_vp ?_; rw [h6_st]
    refine validProg_bind h0_vp ?_; rw [h0_st]
    exact validProg_pure _

/-- In-bounds coordinate helper for `overmarsScanOneProg` (`d = (((wp, base), b), cur)`). -/
@[irreducible] private def overmarsScanInBoundsProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let z1 ← pure 1
    let inL ← checkCoordInLiveGenProg (((wp.1, base), b), cur)
    if inL = z1 then
      overmarsInsertCoordGenProg (((wp, base), b), cur)
    else
      overmarsIncCurGenProg (((wp.1, base), b), cur)

private theorem realizes_overmarsScanInBounds :
    Realizes .exact overmarsScanInBoundsProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        OvermarsScanOnePre w (((wp, base), b), ()) s ∧
        cur = readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 6) ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 0))
      (fun _ _ => 0) := by
  unfold overmarsScanInBoundsProg
  have hcl := realizes_checkCoordInLiveGen
  have hic := realizes_overmarsInsertCoordGen
  have hinc := realizes_overmarsIncCurGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, heq_wp, hseed, hrep, hb, hce_or, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩, hcur_eq0, hcur_lt0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rw [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth]
      at hcur_eq0 hcur_lt0
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    have hbm0 : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
        (16 * b) = fs.bktCount b := hbm.1
    rw [hbm.2.2.2.2.2.2.1] at hcur_eq0
    rw [hbm.1] at hcur_lt0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    obtain ⟨hcl_st, _, _, _⟩ :=
      checkCoordInLiveGenProg_spec henv hrep hce_or hb hcur_tot (s := s)
    simp only [hcp_eq] at *
    simp only [hcl_st] at *
    try simp only [wp_large_M hth, wp_large_nMax hth, wp_large_offBktMeta hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce_or, hb, hcur_tot⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
        hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩
    | exact hbm.2.2.2.2.2.2.1.symm ▸ hcur_eq0
    | (rw [hbm0]; exact hcur_lt0)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | omega
  )

/-- Single coordinate scan step `overmarsScanOneProg` (`p = (((wp, base), b), ())`). -/
private def overmarsScanOneProg : ((WhpParams × ℕ) × ℕ) × Unit → Memory.Prog Unit
  | (((wp, base), b), _) => do
    let cc ← overmarsReadCurCntGenProg ((wp.1, base), b)
    if cc.1 < cc.2 then
      overmarsScanInBoundsProg (((wp, base), b), cc.1)
    else
      overmarsIncCurGenProg (((wp.1, base), b), cc.1)

private theorem memoryCost_overmarsScanOneProg_pos (p : ((WhpParams × ℕ) × ℕ) × Unit)
    (s : Memory.State) :
    1 ≤ memoryCost (overmarsScanOneProg p) s := by
  rcases p with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
  unfold overmarsScanOneProg overmarsReadCurCntGenProg readBktFieldGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedGen]
  omega

private theorem realizes_overmarsScanOne :
    Realizes .exact overmarsScanOneProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × Unit))
      (WordEncoding.encode (α := Unit))
      OvermarsScanOnePre
      (fun _ _ => 0) := by
  unfold overmarsScanOneProg
  have hrc := realizes_overmarsReadCurCntGen
  have hib := realizes_overmarsScanInBounds
  have hinc := realizes_overmarsIncCurGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, heq_wp, hseed, hrep, hb, hce_or, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hcc_st, hcc_res, _, _⟩ := overmarsReadCurCntGenProg_spec henv hb hrep (s := s)
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    have hbm0 : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
        (16 * b) = fs.bktCount b := hbm.1
    simp only [hcp_eq] at *
    simp only [hcc_st, hcc_res] at *
    try simp only [wp_large_M hth, wp_large_nMax hth, wp_large_offBktMeta hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
        hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩
    | exact hbm.2.2.2.2.2.2.1.symm
    | (rw [hbm0]; omega)
    | exact hcur_n
  )

private theorem overmarsScanOneProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {omMap : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hor : fs.overmarsRole b < 3)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hcur_n : fs.overmarsCursor b < n_max)
    (hins_lt : fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsScanOneProg (((mkWhpParams c U V w n_max, base), b), ())
    let s' := (Memory.spec 0).clientState s prog
    let fs1 := overmarsScanSteps c U n_max θ b 1 fs
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 2454 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs1 s s' ∧
    fs1.curEp = fs.curEp ∧
    fs1.overmarsRole b = fs.overmarsRole b ∧
    fs1.bktCount b = fs.bktCount b ∧
    fs1.quotArr = fs.quotArr ∧
    fs1.backPtr = fs.backPtr ∧
    fs1.overmarsCursor b = fs.overmarsCursor b + 1 ∧
    fs1.overmarsInsCount b ≤ fs.overmarsInsCount b + 1 ∧
    ∃ omMap1, ValidWhpSlice n_max (fs1.overmarsInsCount b)
      (fs1.slices (fs1.overmarsSliceIdx b)) omMap1 := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ numBucketsWhp n_max)).trans hML12
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hcc_st, hcc_res, hcc_mc, hcc_vp⟩ :=
    overmarsReadCurCntGenProg_spec henv hb hrep (s := s)
  set cur := fs.overmarsCursor b
  dsimp only
  unfold overmarsScanOneProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  dsimp only [overmarsScanSteps]
  by_cases hcur_lt : cur < fs.bktCount b
  · have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt.trans_le hcnt_le
    have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
      have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
      rw [two_pow_valLaneBitsWhp]; omega
    obtain ⟨hcl_st, hcl_res, hcl_mc, hcl_vp⟩ :=
      checkCoordInLiveGenProg_spec henv hrep hce_or hb hcur_tot (s := s)
    by_cases hinL : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true
    · have hcond : cur < fs.bktCount b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true :=
        ⟨hcur_lt, hinL⟩
      rw [ite_eq_left hcond]
      rw [ite_eq_left hinL] at hcl_res
      obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
        overmarsReadScanInfoGenProg_spec henv hb hrep (s := s)
      have hbp_cur : capFrontWhp n_max ≤ cur → fs.backPtr b (cur - capFrontWhp n_max) <
          poolSizeWhp n_max := fun hcf => hbp_v _ (by omega)
      obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
        fpAtGenProg_spec henv hseed hrep hb hcur_tot hbp_cur (salt := fs.bktSalt b) (s := s)
      have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
        unfold FastState.overmarsSliceIdx; omega
      set fp := fs.fpAt c U n_max θ (fs.bktSalt b) b cur
      obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
        btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om
          (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val (s := s)
      set s_bi := (Memory.spec 0).clientState s
        (btreeInsertGenProg ((((cp, base), fs.overmarsSliceIdx b), fp), cur))
      obtain ⟨hmb_st, hmb_res, hmb_mc, hmb_vp⟩ :=
        mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base)
          hth s_bi
      obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ :=
        overmarsWriteCurInsRtProg_fastStep henv hb (by omega : cur + 1 ≤ n_max)
          (by omega : fs.overmarsInsCount b + 1 ≤ n_max) hbi_step.2.1 hbi_step.2.2.1 (s := s_bi)
      have hv_om1 := (hv_om.insert_spec hth hins_lt.le
        (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val).2
      have hs'_eq : (Memory.spec 0).clientState s
          (overmarsReadCurCntGenProg ((cp, base), b) >>= fun cc =>
            if cc.1 < cc.2 then
              overmarsScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cc.1)
            else
              overmarsIncCurGenProg (((cp, base), b), cc.1)) =
          (Memory.spec 0).clientState s_bi
            (overmarsWriteCurInsRtProg
              (((mkBktMetaRt c U V w n_max base, b), cur + 1), fs.overmarsInsCount b + 1)) := by
        rw [clientState_bind, hcc_st, hcc_res]; dsimp only
        rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        rw [clientState_bind, hcl_st, hcl_res]; simp only [↓reduceIte]
        unfold overmarsInsertCoordGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        rw [clientState_bind, hri_st, hri_res]; dsimp only
        rw [clientState_bind, hfp_st, hfp_res, clientState_bind]
        dsimp only [s_bi, cp] at hmb_st hmb_res ⊢
        rw [clientState_bind, hmb_st, hmb_res]
      rw [hs'_eq]
      refine ⟨?_, ?_, hbi_step.trans hwc_step, rfl, rfl, rfl, rfl, rfl,
        Function.update_self _ _ _, (Function.update_self _ _ _).le,
        ⟨_, by
          change ValidWhpSlice n_max
            (Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) b)
            (Function.update fs.slices (fs.overmarsSliceIdx b) _ (fs.overmarsSliceIdx b)) _
          rw [Function.update_self, Function.update_self]
          exact hv_om1⟩⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcc_st, hcc_res, hcc_mc]; dsimp only; rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcl_st, hcl_res, hcl_mc]; simp only [↓reduceIte]
        unfold overmarsInsertCoordGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hri_st, hri_res, hri_mc]; dsimp only
        rw [hfp_st, hfp_res]
        have hfp_mc' : memoryCost
            (fpAtGenProg ((((mkWhpParams c U V w n_max, base), fs.bktSalt b), b), cur)) s ≤
            2 * hashEvalCostWhp c + 4 := hfp_mc
        dsimp only [fp, s_bi, cp] at hmb_st hmb_res hmb_mc hbi_mc hwc_mc ⊢
        rw [hmb_st, hmb_res, hmb_mc]
        omega
      · refine validProg_bind hcc_vp ?_; rw [hcc_st, hcc_res]; dsimp only
        rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]; simp only [pure_bind]
        refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res]; simp only [↓reduceIte]
        unfold overmarsInsertCoordGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]; simp only [pure_bind]
        refine validProg_bind hri_vp ?_; rw [hri_st, hri_res]; dsimp only
        refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
        refine validProg_bind hbi_vp ?_
        refine validProg_bind hmb_vp ?_; rw [hmb_st, hmb_res]
        exact hwc_vp
    · have hncond : ¬(cur < fs.bktCount b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true) :=
        fun ⟨_, h⟩ => hinL h
      rw [ite_eq_right hncond]
      rw [ite_eq_right hinL] at hcl_res
      obtain ⟨hw6_mc, hw6_vp, hw6_step⟩ :=
        writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10)
          (by omega : cur + 1 ≤ n_max) hseed hrep (s := s)
      have hs'_eq : (Memory.spec 0).clientState s
          (overmarsReadCurCntGenProg ((cp, base), b) >>= fun cc =>
            if cc.1 < cc.2 then
              overmarsScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cc.1)
            else
              overmarsIncCurGenProg (((cp, base), b), cc.1)) =
          (Memory.spec 0).clientState s
            (writeBktFieldGenProg ((((cp, base), b), 6), cur + 1)) := by
        rw [clientState_bind, hcc_st, hcc_res]; dsimp only
        rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg overmarsIncCurGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]; simp only [pure_bind]
        rw [clientState_bind, hcl_st, hcl_res]; simp only [zero_ne_one, ↓reduceIte]
      rw [hs'_eq]
      refine ⟨?_, ?_, hw6_step, rfl, rfl, rfl, rfl, rfl,
        Function.update_self _ _ _, Nat.le_succ _, ⟨omMap, hv_om⟩⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcc_st, hcc_res, hcc_mc]; dsimp only; rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg overmarsIncCurGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcl_st, hcl_res, hcl_mc]; simp only [zero_ne_one, ↓reduceIte]
        dsimp only [cp] at hw6_mc ⊢; omega
      · refine validProg_bind hcc_vp ?_; rw [hcc_st, hcc_res]; dsimp only
        rw [ite_eq_left hcur_lt]
        unfold overmarsScanInBoundsProg overmarsIncCurGenProg; dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]; simp only [pure_bind]
        refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res]
        simp only [zero_ne_one, ↓reduceIte]; exact hw6_vp
  · have hncond : ¬(cur < fs.bktCount b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true) :=
      fun ⟨h, _⟩ => hcur_lt h
    rw [ite_eq_right hncond]
    obtain ⟨hw6_mc, hw6_vp, hw6_step⟩ :=
      writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10)
        (by omega : cur + 1 ≤ n_max) hseed hrep (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (overmarsReadCurCntGenProg ((cp, base), b) >>= fun cc =>
          if cc.1 < cc.2 then
            overmarsScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cc.1)
          else
            overmarsIncCurGenProg (((cp, base), b), cc.1)) =
        (Memory.spec 0).clientState s
          (writeBktFieldGenProg ((((cp, base), b), 6), cur + 1)) := by
      rw [clientState_bind, hcc_st, hcc_res]; dsimp only
      rw [ite_eq_right hcur_lt]
      unfold overmarsIncCurGenProg; simp only [pure_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, hw6_step, rfl, rfl, rfl, rfl, rfl,
      Function.update_self _ _ _, Nat.le_succ _, ⟨omMap, hv_om⟩⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hcc_st, hcc_res, hcc_mc]; dsimp only; rw [ite_eq_right hcur_lt]
      unfold overmarsIncCurGenProg; simp only [pure_bind]
      dsimp only [cp] at hw6_mc ⊢; omega
    · refine validProg_bind hcc_vp ?_; rw [hcc_st, hcc_res]; dsimp only
      rw [ite_eq_right hcur_lt]
      unfold overmarsIncCurGenProg; simp only [pure_bind]
      exact hw6_vp

/-- Bounded-fuel Overmars scan loop via `Realizes.iterate₀`. -/
@[irreducible] private def overmarsScanLoopGenProg (p : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ) :
    Memory.Prog Unit :=
  iterate overmarsScanOneProg p.1.1 p.2 p.1.2

private theorem realizes_overmarsScanLoopGen :
    Realizes .exact overmarsScanLoopGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w p s => iterationSafe overmarsScanOneProg OvermarsScanOnePre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold overmarsScanLoopGenProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
    (WordEncoding.encode (α := Unit))
    realizes_overmarsScanOne
    memoryCost_overmarsScanOneProg_pos

private theorem overmarsScanLoopGenProg_spec {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let d0 := ((mkWhpParams c U V w n_max, base), b)
    ∀ rem (fs : FastState) (omMap : ℕ → Option ℕ) (s : Memory.State),
      (fs.curEp = 0 ∨ fs.curEp = 1) →
      fs.overmarsRole b < 3 →
      fs.bktCount b ≤ totalLocalCoordsWhp n_max →
      fs.overmarsCursor b + rem ≤ n_max →
      fs.overmarsInsCount b + rem ≤ 8 * (slabScale n_max) ^ 12 →
      (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) →
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) →
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap →
      SeedWhpMemRep base c U w n_max θ s.mem →
      FastMemRep base c U V w n_max fs s.mem →
      let prog := overmarsScanLoopGenProg ((d0, ()), rem)
      let s' := (Memory.spec 0).clientState s prog
      let fs' := overmarsScanSteps c U n_max θ b rem fs
      iterationSafe overmarsScanOneProg OvermarsScanOnePre w d0 rem () s ∧
      memoryCost prog s ≤ rem * (2 * hashEvalCostWhp c + 2454) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      FastStateStep base c U V w n_max θ fs' s s' := by
  intro d0 rem
  induction rem with
  | zero =>
    intro fs omMap s _ _ _ _ _ _ _ _ hseed hrep
    unfold overmarsScanLoopGenProg
    exact ⟨trivial, Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩
  | succ rem ih =>
    intro fs omMap s hce hor hcnt hcur_n hins_ub hq_all hbp_v hv_om hseed hrep
    have hpre1 : OvermarsScanOnePre w (d0, ()) s :=
      ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce, hor,
        hcnt, by omega, by omega, hq_all, hbp_v, hv_om⟩
    obtain ⟨hmc1, hvp1, hstep1, hce1, hor1, hcnt1, hq1, hbp1, hcur1, hins1, omMap1, hv_om1⟩ :=
      overmarsScanOneProg_fastStep henv hb hce hor hcnt (by omega) (by omega) hbp_v hv_om
        hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s (overmarsScanOneProg (d0, ()))
    set fs1 := overmarsScanSteps c U n_max θ b 1 fs
    obtain ⟨hsafe_r, hmc_r, hvp_r, hstep_r⟩ :=
      ih fs1 omMap1 s1 (hce1 ▸ hce) (hor1 ▸ hor) (hcnt1 ▸ hcnt)
        (by omega) (by omega) (fun i hi => hq1 ▸ hq_all i hi)
        (fun k hk => hbp1 ▸ hbp_v k (hcnt1 ▸ hk)) hv_om1 hstep1.2.1 hstep1.2.2.1
    have hu_eq : (Memory.spec 0).clientResult s (overmarsScanOneProg (d0, ())) = () := rfl
    dsimp only
    unfold overmarsScanLoopGenProg at hmc_r hvp_r hstep_r ⊢
    dsimp only [iterate] at hmc_r hvp_r hstep_r ⊢
    have hst_all : (Memory.spec 0).clientState s
        (overmarsScanOneProg (d0, ()) >>= fun u => iterate overmarsScanOneProg d0 rem u) =
        (Memory.spec 0).clientState s1 (iterate overmarsScanOneProg d0 rem ()) := by
      rw [clientState_bind, hu_eq]
    rw [hst_all]
    refine ⟨⟨hpre1, ?_⟩, ?_, validProg_bind hvp1 hvp_r, hstep1.trans hstep_r⟩
    · rw [clientState_width, clientResult_width]; exact hsafe_r
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hu_eq]
      calc memoryCost (overmarsScanOneProg (d0, ())) s +
            memoryCost (iterate overmarsScanOneProg d0 rem ()) s1
          ≤ (2 * hashEvalCostWhp c + 2454) + rem * (2 * hashEvalCostWhp c + 2454) :=
            Nat.add_le_add hmc1 hmc_r
        _ = (rem + 1) * (2 * hashEvalCostWhp c + 2454) := by ring

private theorem overmarsScanLoopGenProg_safe {c U V w n_max base b rem : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {omMap : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hor : fs.overmarsRole b < 3)
    (hcnt : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hcur : fs.overmarsCursor b + rem ≤ n_max)
    (hins : fs.overmarsInsCount b + rem ≤ 8 * (slabScale n_max) ^ 12)
    (hq : ∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max)
    (hbp : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    iterationSafe overmarsScanOneProg OvermarsScanOnePre w
      ((mkWhpParams c U V w n_max, base), b) rem () s :=
  (overmarsScanLoopGenProg_spec henv hb rem fs omMap s hce hor hcnt hcur hins hq hbp hv_om
    hseed hrep).1

/-- Inner swap action of `overmarsFinishSwapGenProg` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsDoSwapGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let bm ← mkBktMetaRtProg (cp, base)
    overmarsSwapRolesRtProg (bm, b)
    setOvermarsActRtProg ((bm, b), z0)

private theorem realizes_overmarsDoSwapGen :
    Realizes .exact overmarsDoSwapGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsDoSwapGenProg
  have hmb := realizes_mkBktMetaRt
  have hsr := realizes_overmarsSwapRolesRt
  have hsa := realizes_setOvermarsActRt
  realize
  rcases d with ⟨⟨cp, base⟩, b⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  rw [wp_large_M hth] at hb
  simp only [hmb_st, hmb_res] at *
  exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩

/-- Role-swap completion substep of `overmarsStep` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsFinishSwapGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let cnt ← readBktFieldGenProg (((cp, base), b), 0)
    let cur ← readBktFieldGenProg (((cp, base), b), 6)
    if cnt ≤ cur then
      overmarsDoSwapGenProg ((cp, base), b)
    else
      pure ()

private theorem realizes_overmarsFinishSwapGen :
    Realizes .exact overmarsFinishSwapGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsFinishSwapGenProg
  have hrb := realizes_readBktFieldGen
  have hds := realizes_overmarsDoSwapGen
  have hcs_r : ∀ x (s' : Memory.State),
      (Memory.spec 0).clientState s' (readBktFieldGenProg x) = s' := by
    rintro ⟨⟨⟨_, _⟩, _⟩, _⟩ _; unfold readBktFieldGenProg; simp only [pure_bind]; rfl
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    simp only [hcs_r] at *
    simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem overmarsFinishSwapGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs1 : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs1.liveRole b ≤ n_max) (hor : fs1.overmarsRole b ≤ n_max)
    (hins : fs1.overmarsInsCount b ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs1 s.mem) :
    let prog := overmarsFinishSwapGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let fs2 : FastState :=
      if fs1.bktCount b ≤ fs1.overmarsCursor b then
        let oldLive := fs1.liveRole b
        let oldOm := fs1.overmarsRole b
        { fs1 with
          liveRole := Function.update fs1.liveRole b oldOm
          overmarsRole := Function.update fs1.overmarsRole b oldLive
          liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
          overmarsActive := Function.update fs1.overmarsActive b 0
          overmarsCursor := Function.update fs1.overmarsCursor b 0
          overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
      else fs1
    memoryCost prog s ≤ 34 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs2 s s' := by
  have hth := henv.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨h0_st, h0_res, h0_mc, h0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  obtain ⟨h6_st, h6_res, h6_mc, h6_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 6 < 10) hrep (s := s)
  simp only [getBktField] at h0_res h6_res
  dsimp only
  unfold overmarsFinishSwapGenProg
  by_cases hdone : fs1.bktCount b ≤ fs1.overmarsCursor b
  · rw [ite_eq_left hdone]
    obtain ⟨hmb_st, hmb_res, hmb_mc, hmb_vp⟩ :=
      mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base)
        hth s
    obtain ⟨hsr_mc, hsr_vp, hsr_step⟩ :=
      overmarsSwapRolesRtProg_fastStep henv hb hlr hor hins hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s
      (overmarsSwapRolesRtProg (mkBktMetaRt c U V w n_max base, b))
    obtain ⟨hsa_mc, hsa_vp, hsa_step⟩ :=
      setOvermarsActRtProg_fastStep henv hb (Nat.zero_le n_max)
        hsr_step.2.1 hsr_step.2.2.1 (s := s1)
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
          readBktFieldGenProg (((cp, base), b), 6) >>= fun cur =>
          if cnt ≤ cur then overmarsDoSwapGenProg ((cp, base), b) else pure ()) =
        (Memory.spec 0).clientState s1
          (setOvermarsActRtProg ((mkBktMetaRt c U V w n_max base, b), 0)) := by
      rw [clientState_bind, h0_st, h0_res, clientState_bind, h6_st, h6_res,
        ite_eq_left hdone]
      unfold overmarsDoSwapGenProg; simp only [pure_bind]
      rw [clientState_bind, hmb_st, hmb_res, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, hsr_step.trans hsa_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h0_st, h0_res, h0_mc, h6_st, h6_res, h6_mc, ite_eq_left hdone]
      unfold overmarsDoSwapGenProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmb_st, hmb_res, hmb_mc]
      dsimp only [s1, cp] at hsr_mc hsa_mc ⊢
      omega
    · refine validProg_bind h0_vp ?_; rw [h0_st, h0_res]
      refine validProg_bind h6_vp ?_; rw [h6_st, h6_res, ite_eq_left hdone]
      unfold overmarsDoSwapGenProg; simp only [pure_bind]
      refine validProg_bind hmb_vp ?_; rw [hmb_st, hmb_res]
      exact validProg_bind hsr_vp hsa_vp
  · rw [ite_eq_right hdone]
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
          readBktFieldGenProg (((cp, base), b), 6) >>= fun cur =>
          if cnt ≤ cur then overmarsDoSwapGenProg ((cp, base), b) else pure ()) = s := by
      rw [clientState_bind, h0_st, h0_res, clientState_bind, h6_st, h6_res,
        ite_eq_right hdone]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h0_st, h0_res, h0_mc, h6_st, h6_res, h6_mc, ite_eq_right hdone]
      simp only [memoryCost_pure]; omega
    · refine validProg_bind h0_vp ?_; rw [h0_st, h0_res]
      refine validProg_bind h6_vp ?_; rw [h6_st, h6_res, ite_eq_right hdone]
      exact validProg_pure _

/-- Complete `overmarsStep` `Memory.Prog` subroutine (`d = ((wp, base), b)`). -/
@[irreducible] def overmarsStepGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog Unit
  | ((wp, base), b) => do
    let z1 ← pure 1
    let n16 ← pure 16
    overmarsActivateGenProg ((wp.1, base), b)
    let act ← readBktFieldGenProg (((wp.1, base), b), 5)
    if act = z1 then do
      overmarsScanLoopGenProg ((((wp, base), b), ()), n16)
      overmarsFinishSwapGenProg ((wp.1, base), b)
    else
      pure ()

/-- Minimal structural bounds on `fs` sufficient to execute `overmarsStepGenProg` safely on
bucket `b`. -/
@[expose] def OvermarsBucketStepBounds (U n_max b : ℕ) (fs : FastState) : Prop :=
  b < numBucketsWhp n_max ∧
  (fs.curEp = 0 ∨ fs.curEp = 1) ∧
  fs.liveRole b < 3 ∧
  fs.overmarsRole b < 3 ∧
  fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
  (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
  (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
  ((overmarsAfterActivate n_max b fs).overmarsActive b = 1 →
    (overmarsAfterActivate n_max b fs).overmarsCursor b + 16 ≤ n_max ∧
    (overmarsAfterActivate n_max b fs).overmarsInsCount b + 16 ≤ 8 * (slabScale n_max) ^ 12 ∧
    ∃ omMap0, ValidWhpSlice n_max ((overmarsAfterActivate n_max b fs).overmarsInsCount b)
      ((overmarsAfterActivate n_max b fs).slices
        ((overmarsAfterActivate n_max b fs).overmarsSliceIdx b)) omMap0)

/-- `CoreFastInv` + `PreOvermarsBucketInv` immediately yield `OvermarsBucketStepBounds`. -/
theorem OvermarsBucketStepBounds.of_core_and_pre {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hb : b < numBucketsWhp n_max)
    (hom : PreOvermarsBucketInv c U n_max θ fs b) :
    OvermarsBucketStepBounds U n_max b fs := by
  have h2tl := (large_index_bounds hc.hth).2.2.1
  have hL2 := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_tl := hc.bktCount_le b hb
  have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    hcnt_tl.trans totalLocalCoordsWhp_le_three_mul
  refine ⟨hb, hc.curEp_or, (hc.roles_valid b hb).1, (hc.roles_valid b hb).2.1,
    hcnt_tl, fun i _ => (hc.qv_global i).1,
    fun k hk => (hc.backPtr_valid b hb k hk).1, ?_⟩
  unfold overmarsAfterActivate
  intro ha1
  rcases hom with ⟨ha0, _⟩ | ⟨ha_act, _, hcur_le, _, hins_le, omMap0, hv0, _⟩
  · by_cases htrig : 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
    · have hc0 : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b :=
        ⟨ha0, htrig⟩
      rw [ite_eq_left hc0]
      dsimp only [FastState.overmarsSliceIdx]
      simp only [Function.update_self]
      exact ⟨by omega, by omega, ⟨fun _ => none, validWhpSlice_zero _ 0 _⟩⟩
    · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b) :=
        fun ⟨_, h⟩ => htrig h
      rw [ite_eq_right hnc0] at ha1; omega
  · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b) :=
      by omega
    rw [ite_eq_right hnc0]
    exact ⟨by omega, by omega, ⟨omMap0, hv0⟩⟩

/-- Precondition for `overmarsStepGenProg`. -/
@[expose] def OvermarsStepPre (w : ℕ) : (WhpParams × ℕ) × ℕ → Memory.State → Prop
  | ((wp, base), b), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      OvermarsBucketStepBounds U n_max b fs

private theorem overmarsScanSteps_roles_and_ins (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (st : FastState),
      (overmarsScanSteps c U n_max θ b k st).liveRole b = st.liveRole b ∧
      (overmarsScanSteps c U n_max θ b k st).overmarsRole b = st.overmarsRole b ∧
      (overmarsScanSteps c U n_max θ b k st).overmarsInsCount b ≤ st.overmarsInsCount b + k := by
  intro k
  induction k with
  | zero =>
    intro st
    dsimp only [overmarsScanSteps]
    exact ⟨rfl, rfl, Nat.le_add_right _ _⟩
  | succ k ih =>
    intro st
    dsimp only [overmarsScanSteps]
    by_cases hcond : st.overmarsCursor b < st.bktCount b ∧
        inLiveTree st.rebStage st.oldEp (st.rebDoneFlag b) (st.locState b (st.overmarsCursor b)) =
          true
    · rw [ite_eq_left hcond]
      set st1 : FastState :=
        { st with
          slices := Function.update st.slices (st.overmarsSliceIdx b)
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (st.slices (st.overmarsSliceIdx b))
              (st.fpAt c U n_max θ (st.bktSalt b) b (st.overmarsCursor b))
              (st.overmarsCursor b))
          overmarsCursor := Function.update st.overmarsCursor b (st.overmarsCursor b + 1)
          overmarsInsCount := Function.update st.overmarsInsCount b (st.overmarsInsCount b + 1) }
      obtain ⟨r1, r2, r3⟩ := ih st1
      dsimp only [st1] at r1 r2 r3 ⊢
      rw [Function.update_self] at r3
      exact ⟨r1, r2, by omega⟩
    · rw [ite_eq_right hcond]
      set st1 : FastState :=
        { st with overmarsCursor := Function.update st.overmarsCursor b (st.overmarsCursor b + 1) }
      obtain ⟨r1, r2, r3⟩ := ih st1
      dsimp only [st1] at r1 r2 r3 ⊢
      exact ⟨r1, r2, by omega⟩

theorem realizes_overmarsStepGen :
    Realizes .exact overmarsStepGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      OvermarsStepPre
      (fun _ _ => 0) := by
  unfold overmarsStepGenProg
  have hoa := realizes_overmarsActivateGen
  have hrb := realizes_readBktFieldGen
  have hsl := realizes_overmarsScanLoopGen
  have hfs := realizes_overmarsFinishSwapGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, b⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep,
      ⟨hb, hce_or, _, hor, hcnt_le, hq_all, hbp_v, hscan16⟩⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hoa_step⟩ := overmarsActivateGenProg_fastStep henv hb hor hseed hrep (s := s)
    have hrep0 : FastMemRep base c U V w n_max (overmarsAfterActivate n_max b fs)
        ((Memory.spec 0).clientState s
          (overmarsActivateGenProg ((mkWhpCoreParams c U V w n_max, base), b))).mem :=
      hoa_step.2.2.1
    obtain ⟨h5_st, h5_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep0
        (s := (Memory.spec 0).clientState s
          (overmarsActivateGenProg ((mkWhpCoreParams c U V w n_max, base), b)))
    simp only [getBktField] at h5_res
    simp only [hcp_eq] at *
    simp only [h5_st, h5_res] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | (obtain ⟨hcur16, hins16, omMap0, hv0⟩ := hscan16 (by assumption)
       have hce0 : (overmarsAfterActivate n_max b fs).curEp = fs.curEp := by
         unfold overmarsAfterActivate; split_ifs <;> rfl
       have hor0 : (overmarsAfterActivate n_max b fs).overmarsRole b = fs.overmarsRole b := by
         unfold overmarsAfterActivate; split_ifs <;> rfl
       have hcnt0 : (overmarsAfterActivate n_max b fs).bktCount b = fs.bktCount b := by
         unfold overmarsAfterActivate; split_ifs <;> rfl
       have hq0 : (overmarsAfterActivate n_max b fs).quotArr = fs.quotArr := by
         unfold overmarsAfterActivate; split_ifs <;> rfl
       have hbp0 : (overmarsAfterActivate n_max b fs).backPtr = fs.backPtr := by
         unfold overmarsAfterActivate; split_ifs <;> rfl
       exact overmarsScanLoopGenProg_safe henv hb
         (hce0 ▸ hce_or) (hor0 ▸ hor) (hcnt0 ▸ hcnt_le)
         hcur16 hins16 (fun i hi => hq0 ▸ hq_all i hi)
         (fun k hk => hbp0 ▸ hbp_v k (hcnt0 ▸ hk))
         hv0 hoa_step.2.1 hrep0)
  )

private theorem overmarsStep_eq (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ)
    (fs : FastState) :
    overmarsStep c U n_max θ b fs =
      let fs0 := overmarsAfterActivate n_max b fs
      if fs0.overmarsActive b = 1 then
        let fs1 := overmarsScanSteps c U n_max θ b 16 fs0
        if fs1.bktCount b ≤ fs1.overmarsCursor b then
          { fs1 with
            liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
            overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
            liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
            overmarsActive := Function.update fs1.overmarsActive b 0
            overmarsCursor := Function.update fs1.overmarsCursor b 0
            overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
        else fs1
      else fs0 := by
  unfold overmarsStep overmarsAfterActivate
  rfl

theorem overmarsStepGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hbnds : OvermarsBucketStepBounds U n_max b fs)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 39326 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fs) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hn4 := four_le_of_whpThreshold_le hth
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ numBucketsWhp n_max)).trans hML12
  rcases hbnds with ⟨hb, hce_or, hlr, hor, hcnt_le, hq_all, hbp_v, hscan16⟩
  obtain ⟨hoa_mc, hoa_vp, hoa_step⟩ :=
    overmarsActivateGenProg_fastStep henv hb hor hseed hrep (s := s)
  set cp := mkWhpCoreParams c U V w n_max
  set s0 := (Memory.spec 0).clientState s (overmarsActivateGenProg ((cp, base), b))
  have hrep0 : FastMemRep base c U V w n_max (overmarsAfterActivate n_max b fs) s0.mem :=
    hoa_step.2.2.1
  obtain ⟨h5_st, h5_res, h5_mc, h5_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep0 (s := s0)
  simp only [getBktField] at h5_res
  dsimp only
  unfold overmarsStepGenProg
  rw [overmarsStep_eq]
  generalize hk16_eq : (16 : ℕ) = k16
  have hk16 : k16 ≤ 16 := hk16_eq ▸ le_rfl
  clear hk16_eq
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  set fs0 := overmarsAfterActivate n_max b fs
  by_cases ha1 : fs0.overmarsActive b = 1
  · rw [ite_eq_left ha1]
    obtain ⟨hcur16, hins16, omMap0, hv0⟩ := hscan16 ha1
    have hce0 : fs0.curEp = fs.curEp := by unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    have hor0 : fs0.overmarsRole b = fs.overmarsRole b := by
      unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    have hlr0 : fs0.liveRole b = fs.liveRole b := by
      unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    have hcnt0 : fs0.bktCount b = fs.bktCount b := by
      unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    have hq0 : fs0.quotArr = fs.quotArr := by unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    have hbp0 : fs0.backPtr = fs.backPtr := by unfold fs0 overmarsAfterActivate; split_ifs <;> rfl
    obtain ⟨_, hsl_mc, hsl_vp, hsl_step⟩ :=
      overmarsScanLoopGenProg_spec henv hb k16 fs0 omMap0 s0
        (hce0 ▸ hce_or) (hor0 ▸ hor) (hcnt0 ▸ hcnt_le)
        (by omega) (by omega) (fun i hi => hq0 ▸ hq_all i hi)
        (fun k' hk' => hbp0 ▸ hbp_v k' (hcnt0 ▸ hk'))
        hv0 hoa_step.2.1 hrep0
    obtain ⟨r1, r2, r3⟩ := overmarsScanSteps_roles_and_ins c U n_max θ b k16 fs0
    obtain ⟨hfs_mc, hfs_vp, hfs_step⟩ :=
      overmarsFinishSwapGenProg_fastStep henv hb
        (by omega) (by omega) (by omega) hsl_step.2.1 hsl_step.2.2.1
        (s := (Memory.spec 0).clientState s0
          (overmarsScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), k16)))
    have hs'_eq : (Memory.spec 0).clientState s
        (overmarsActivateGenProg ((cp, base), b) >>= fun _ =>
          readBktFieldGenProg (((cp, base), b), 5) >>= fun act =>
          if act = 1 then
            overmarsScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), k16) >>= fun _ =>
            overmarsFinishSwapGenProg ((cp, base), b)
          else pure ()) =
        (Memory.spec 0).clientState
          ((Memory.spec 0).clientState s0
            (overmarsScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), k16)))
          (overmarsFinishSwapGenProg ((cp, base), b)) := by
      rw [clientState_bind, clientState_bind, h5_st, h5_res, ite_eq_left ha1,
        clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hoa_step.trans hsl_step).trans hfs_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost (overmarsActivateGenProg ((cp, base), b)) s +
        (memoryCost (readBktFieldGenProg (((cp, base), b), 5)) s0 + _) ≤ _
      rw [h5_st, h5_res, h5_mc, ite_eq_left ha1]
      simp only [memoryCost_bind]
      dsimp only [cp, s0] at hoa_mc hsl_mc hfs_mc ⊢
      have hk_mul : k16 * (2 * hashEvalCostWhp c + 2454) ≤
          16 * (2 * hashEvalCostWhp c + 2454) := Nat.mul_le_mul_right _ hk16
      omega
    · refine validProg_bind hoa_vp ?_
      refine validProg_bind h5_vp ?_; rw [h5_st, h5_res, ite_eq_left ha1]
      exact validProg_bind hsl_vp hfs_vp
  · rw [ite_eq_right ha1]
    have hs'_eq : (Memory.spec 0).clientState s
        (overmarsActivateGenProg ((cp, base), b) >>= fun _ =>
          readBktFieldGenProg (((cp, base), b), 5) >>= fun act =>
          if act = 1 then
            overmarsScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), k16) >>= fun _ =>
            overmarsFinishSwapGenProg ((cp, base), b)
          else pure ()) = s0 := by
      rw [clientState_bind, clientState_bind, h5_st, h5_res, ite_eq_right ha1]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, hoa_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost (overmarsActivateGenProg ((cp, base), b)) s +
        (memoryCost (readBktFieldGenProg (((cp, base), b), 5)) s0 + _) ≤ _
      rw [h5_st, h5_res, h5_mc, ite_eq_right ha1]
      simp only [memoryCost_pure]
      dsimp only [cp] at hoa_mc ⊢; omega
    · refine validProg_bind hoa_vp ?_
      refine validProg_bind h5_vp ?_; rw [h5_st, h5_res, ite_eq_right ha1]
      exact validProg_pure _


end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
