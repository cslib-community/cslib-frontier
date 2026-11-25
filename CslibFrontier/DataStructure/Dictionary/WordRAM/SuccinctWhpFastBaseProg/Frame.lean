/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg

/-!
# Fast-Mode Transition Frame Invariant (`FastStateStep`) and Large-Regime Bounds

This module defines the compositional transition invariant `FastStateStep` for fast-mode
`Memory.Prog` subroutines on `FastMemRep`, together with:

1. Large-regime index and capacity bounds (`large_index_bounds`, `bufTrie_caps_of_bounds`).
2. `FastStateStep` reflexivity/transitivity, `bTreeSliceMemRep_congr`, and `FastMemRep`
   slice/buffer projections (`FastMemRep.slice_rep`, `FastMemRep.buf_rep`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.FastStateStep`: compositional invariant
  preserving `SeedWhpMemRep`, `FastMemRep`, `frontier`, and memory outside `largeSpaceWhp`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.large_index_bounds`,
  `bTreeSliceMemRep_congr`, `bufTrie_caps_of_bounds`.
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

/-! ## Section 1: Segment and Index Bounds -/

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
    rw [show (slabScale n_max) ^ 12 = slabScale n_max * (slabScale n_max) ^ 11 by ring]
    exact Nat.mul_le_mul_right _ hL2
  have hmcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have hmcf : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
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

/-! ## Section 2: `FastStateStep` and `FastMemRep` Projections -/

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

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
