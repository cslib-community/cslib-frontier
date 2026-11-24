/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpBufferTrie
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpSwarBTreeInsert
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.Probability
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallRegime
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Large-Epoch Metadata Layout and Hashing `RealizesBounded` Primitives

This module defines the word-level memory offsets inside `[metaBase, metaBase + epochMetaWordsWhp
c w N)` for a large hashed epoch (`whpThreshold c ≤ N ≤ U < 2 ^ w`) of the deamortized worst-case
WHP resizable succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]), proves `w`-bit word-fit bounds on every
epoch table dimension and bit-width parameter (`largeEpoch_param_bounds`,
`four_mul_tMin_mul_keyLane_lt_log`), and certifies parameter-free (`¬ReadsWidth`)
`RealizesBounded .exact` `Memory.Prog` implementations for Stage-1 reduced-key, Stage-2 salted
bit-packed double-tabulation, and one-round Feistel evaluators (`subClampProg`,
`oddMulReducedProg`, `evalSaltedBoundedProg`, `feistelSplitBoundedProg`,
`feistelReconBoundedProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.offBktHash`, `offFpHash`,
  `offBktMeta`, `offSlabDir`, `offTailDir`, `offSlabOwner`, `offTailOwner`, `offBTreeMeta`,
  `offBTreeKeys`, `offBTreeVals`, `offTrieChild`, `offTrieNode`, `offTrieItem`, `offPageDir`,
  `offPageTail`, `offEpochEnd`: per-epoch word offsets.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.subClampProg`, `oddMulReducedProg`,
  `evalSaltedBoundedProg`, `feistelSplitBoundedProg`, `feistelReconBoundedProg`: overflow- and
  underflow-free `Memory.Prog` primitives.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.offEpochEnd_eq_epochMetaWordsWhp`,
  `four_mul_tMin_mul_keyLane_lt_log`, `largeEpoch_param_bounds`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.realizesBounded_evalSaltedBounded`,
  `evalSaltedBoundedProg_eq_evalSalted`, `realizesBounded_feistelSplit`,
  `feistelSplitBoundedProg_spec`, `realizesBounded_feistelRecon`, `feistelReconBoundedProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Per-Epoch Metadata Offsets and Word-Fit Bounds -/

/-- Relative word offset (`32`) of the Feistel quotient-to-bucket double-tabulation seed. -/
@[expose] def offBktHash : ℕ := 32

/-- Relative word offset of the salted fingerprint `BitPackedDoubleTabulation` seed. -/
@[expose] def offFpHash (c w N : ℕ) : ℕ :=
  offBktHash + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N)

/-- Relative word offset of the `16 * M`-entry per-bucket scalar table (`ptrB` bits each). -/
@[expose] def offBktMeta (c w N : ℕ) : ℕ :=
  offFpHash c w N +
    BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N)

/-- Relative word offset of the `M * maxSlabsPerBktWhp N`-entry per-bucket slab directory. -/
@[expose] def offSlabDir (c w N : ℕ) : ℕ :=
  offBktMeta c w N + packedWords (16 * numBucketsWhp N) (globalPtrBits N) w

/-- Relative word offset of the `8 * M * slabSizeWhp N`-entry per-bucket tail ring directory. -/
@[expose] def offTailDir (c w N : ℕ) : ℕ :=
  offSlabDir c w N +
    packedWords (numBucketsWhp N * maxSlabsPerBktWhp N) (globalPtrBits N) w

/-- Relative word offset of the `4 * (N / K + 4)`-entry global block-owner directory. -/
@[expose] def offSlabOwner (c w N : ℕ) : ℕ :=
  offTailDir c w N +
    packedWords (8 * numBucketsWhp N * slabSizeWhp N) (globalPtrBits N) w

/-- Relative word offset of the `16 * maxTailWhp N`-entry global tail-owner directory. -/
@[expose] def offTailOwner (c w N : ℕ) : ℕ :=
  offSlabOwner c w N +
    packedWords (4 * (N / slabSizeWhp N + 4)) (globalPtrBits N) w

/-- Relative word offset of the `totalBTreeNodesWhp N`-entry SWAR B+-tree `metaWord` array. -/
@[expose] def offBTreeMeta (c w N : ℕ) : ℕ :=
  offTailOwner c w N + packedWords (16 * maxTailWhp N) (globalPtrBits N) w

/-- Relative word offset of the `totalBTreeNodesWhp N`-entry SWAR B+-tree `keysWord` array. -/
@[expose] def offBTreeKeys (c w N : ℕ) : ℕ :=
  offBTreeMeta c w N + packedWords (totalBTreeNodesWhp N) (nodeMetaBitsWhp N) w

/-- Relative word offset of the `totalBTreeNodesWhp N`-entry SWAR B+-tree `valsWord` array. -/
@[expose] def offBTreeVals (c w N : ℕ) : ℕ :=
  offBTreeKeys c w N + packedWords (totalBTreeNodesWhp N) (keysWordBitsWhp N) w

/-- Words per `BufTrie` child pointer array (`maxTrieNodesWhp c N * 2 ^ bCharWhp N` entries). -/
@[expose] def trieChildWords (c w N : ℕ) : ℕ :=
  packedWords (maxTrieNodesWhp c N * 2 ^ bCharWhp N) (globalPtrBits N) w

/-- Words per `BufTrie` node-metadata array (`6 * maxTrieNodesWhp c N` entries). -/
@[expose] def trieNodeWords (c w N : ℕ) : ℕ :=
  packedWords (6 * maxTrieNodesWhp c N) (globalPtrBits N) w

/-- Words per `BufTrie` item-log array (`6 * qEpochWhp N + 6` entries). -/
@[expose] def trieItemWords (w N : ℕ) : ℕ :=
  packedWords (6 * qEpochWhp N + 6) (globalPtrBits N) w

/-- Relative word offset of `BufTrie` copy `role ∈ {0, 1}`'s child pointer array. -/
@[expose] def offTrieChild (c w N role : ℕ) : ℕ :=
  offBTreeVals c w N + packedWords (totalBTreeNodesWhp N) (valsWordBitsWhp N) w +
    role * trieChildWords c w N

/-- Relative word offset of `BufTrie` copy `role ∈ {0, 1}`'s node-metadata array. -/
@[expose] def offTrieNode (c w N role : ℕ) : ℕ :=
  offTrieChild c w N 2 + role * trieNodeWords c w N

/-- Relative word offset of `BufTrie` copy `role ∈ {0, 1}`'s item-log array. -/
@[expose] def offTrieItem (c w N role : ℕ) : ℕ :=
  offTrieNode c w N 2 + role * trieItemWords w N

/-- Relative word offset of the `PagePairState` page directory (`4 * (N / pgB + 4)` entries). -/
@[expose] def offPageDir (c w N : ℕ) : ℕ :=
  offTrieItem c w N 2

/-- Relative word offset of the `PagePairState` tail directory (`16 * pgB` entries). -/
@[expose] def offPageTail (c w N : ℕ) : ℕ :=
  offPageDir c w N + packedWords (4 * (N / pageSizeWhp N + 4)) (globalPtrBits N) w

/-- Total words spanned by the per-epoch layout (`offPageTail + packedWords (16 * pgB) ptrB w`). -/
@[expose] def offEpochEnd (c w N : ℕ) : ℕ :=
  offPageTail c w N + packedWords (16 * pageSizeWhp N) (globalPtrBits N) w

theorem offEpochEnd_eq_epochMetaWordsWhp {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    offEpochEnd c w N = epochMetaWordsWhp c w N := by
  have hnot : ¬(N < whpThreshold c) := Nat.not_lt.mpr hth
  simp only [epochMetaWordsWhp, hnot, ↓reduceIte, offEpochEnd, offPageTail, offPageDir,
    offTrieItem, offTrieNode, offTrieChild, trieChildWords, trieNodeWords, trieItemWords,
    offBTreeVals, offBTreeKeys, offBTreeMeta, offTailOwner, offSlabOwner, offTailDir, offSlabDir,
    offBktMeta, offFpHash, offBktHash]

/-- Key SWAR non-overflow inequality: `4 * tMinWhp N * keyLaneBitsWhp N < Nat.log 2 N` whenever
`whpThreshold c ≤ N`, guaranteeing that even the full product `ltMask * swarOnes W (2 * tMinWhp N)`
fits strictly inside `⌊log₂ N⌋ < w` bits without overflow. -/
theorem four_mul_tMin_mul_keyLane_lt_log {c N : ℕ} (hth : whpThreshold c ≤ N) :
    4 * tMinWhp N * keyLaneBitsWhp N < Nat.log 2 N := by
  have h8 := eight_le_tMinWhp hth
  have h1 := Dynamic.one_le_logLogFactor N
  have h320 : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have h1280 : 1280 * Dynamic.logLogFactor N ≤ Nat.log 2 N := by
    unfold bCharWhp at h320; omega
  have ht : tMinWhp N = Nat.log 2 N / (160 * Dynamic.logLogFactor N) := by
    unfold tMinWhp at h8 ⊢; omega
  have hmul : tMinWhp N * (160 * Dynamic.logLogFactor N) ≤ Nat.log 2 N := by
    rw [ht]; exact Nat.div_mul_le_self _ _
  have hkl : keyLaneBitsWhp N ≤ 38 * Dynamic.logLogFactor N := by
    unfold keyLaneBitsWhp fpBitsWhp; omega
  calc 4 * tMinWhp N * keyLaneBitsWhp N
      ≤ 4 * tMinWhp N * (38 * Dynamic.logLogFactor N) := Nat.mul_le_mul_left _ hkl
    _ = 152 * (tMinWhp N * Dynamic.logLogFactor N) := by ring
    _ < 160 * (tMinWhp N * Dynamic.logLogFactor N) := by nlinarith
    _ = tMinWhp N * (160 * Dynamic.logLogFactor N) := by ring
    _ ≤ Nat.log 2 N := hmul

private theorem mul_64000_le_two_pow : ∀ d : ℕ, 64000 * (d + 22 + 2) ≤ 2 ^ (d + 22)
  | 0 => by decide
  | d + 1 => by
    have ih := mul_64000_le_two_pow d
    have h22 : 64000 ≤ 2 ^ (d + 22) :=
      (by decide : 64000 ≤ 2 ^ 22).trans (Nat.pow_le_pow_right (by decide) (by omega))
    rw [show d + 1 + 22 = (d + 22) + 1 by omega, Nat.pow_succ]
    omega

/-- Every table entry count and bit-width parameter of a large epoch `whpThreshold c ≤ N ≤ U`
(`U < 2 ^ w`) fits strictly inside `w`-bit words (`≤ N < 2 ^ globalPtrBits N` and `< 2 ^ w`). -/
theorem largeEpoch_param_bounds {c U w N : ℕ} (hth : whpThreshold c ≤ N)
    (hNU : N ≤ U) (hU : Fits w U) :
    N < 2 ^ globalPtrBits N ∧
    globalPtrBits N ≤ w ∧
    Nat.log 2 N < w ∧
    bCharWhp N < w ∧
    bWhp N < w ∧
    fpBitsWhp N < w ∧
    nodeMetaBitsWhp N < w ∧
    keysWordBitsWhp N < w ∧
    valsWordBitsWhp N < w ∧
    BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp N) ≤ N ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp N) ≤ N ∧
    totalBTreeNodesWhp N ≤ N ∧
    maxTrieNodesWhp c N * 2 ^ bCharWhp N ≤ N ∧
    6 * maxTrieNodesWhp c N ≤ N ∧
    6 * qEpochWhp N + 6 ≤ N ∧
    16 * pageSizeWhp N ≤ N ∧
    4 * (N / pageSizeWhp N + 4) ≤ N ∧
    4 * (N / slabSizeWhp N + 4) ≤ N ∧
    8 * numBucketsWhp N * slabSizeWhp N ≤ N ∧
    16 * maxTailWhp N ≤ N := by
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hptr_lt : N < 2 ^ globalPtrBits N := by
    unfold globalPtrBits
    have hle := Nat.le_pow_clog Nat.one_lt_two (N + 1)
    omega
  have hptr_pos : 1 ≤ globalPtrBits N := by
    by_contra h0
    have hzero : globalPtrBits N = 0 := by omega
    rw [hzero] at hptr_lt
    omega
  have hptr_w : globalPtrBits N ≤ w := by
    unfold globalPtrBits
    exact Nat.clog_le_of_le_pow (by unfold Fits at hU; omega)
  have hlog_w : Nat.log 2 N < w := by
    have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
    have hlt_pow : 2 ^ Nat.log 2 N < 2 ^ w := lt_of_le_of_lt (hpow.trans hNU) hU
    exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt_pow
  have h320 : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have hell := Dynamic.one_le_logLogFactor N
  have hbc_log : 4 * bCharWhp N ≤ Nat.log 2 N := by unfold bCharWhp; omega
  have hkl_log := keysWordBitsWhp_lt_log hth
  have hvl_log := valsWordBitsWhp_lt_log hth
  obtain ⟨htb1, htb2, _, htc, htm, htl⟩ := sublinear_table_bits_le hth
  have hbc1 : 1 ≤ bCharWhp N := by omega
  have hb1 : 1 ≤ bWhp N := by unfold bWhp; omega
  have htop_le : BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp N) ≤ N :=
    (Nat.le_mul_of_pos_right _ hbc1).trans htb1
  have hbot_le : BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp N) ≤ N :=
    (Nat.le_mul_of_pos_right _ hb1).trans htb2
  have hbt_le : totalBTreeNodesWhp N ≤ N := by
    have hbm := bMinWhp_le_log hth
    have hbmin := le_bMinWhp c
    have hn4 := four_le_of_whpThreshold_le hth
    set m := Nat.log 2 N
    have hm_ge : 2 ^ 22 ≤ m := (by decide : 2 ^ 22 ≤ 6553600).trans (hbmin.trans hbm)
    have hj_ge : 22 ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two hm_ge
    have hell_le : Dynamic.logLogFactor N ≤ Nat.log 2 m + 2 := by
      unfold Dynamic.logLogFactor
      rw [max_eq_left hn4]
      have hlt1 : N < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
      have hcl1 : Nat.clog 2 N ≤ m + 1 := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hlt1.le
      have hlt2 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two m
      refine (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr ?_
      rw [Nat.pow_succ]; omega
    have h64k : 64000 * Dynamic.logLogFactor N ≤ m := by
      calc 64000 * Dynamic.logLogFactor N
          ≤ 64000 * (Nat.log 2 m + 2) := Nat.mul_le_mul_left _ hell_le
        _ = 64000 * ((Nat.log 2 m - 22) + 22 + 2) := by congr 1; omega
        _ ≤ 2 ^ ((Nat.log 2 m - 22) + 22) := mul_64000_le_two_pow _
        _ = 2 ^ Nat.log 2 m := by congr 1; omega
        _ ≤ m := Nat.pow_log_le_self 2 (by omega)
    have ht400 : 400 ≤ tMinWhp N := by
      have hdiv : 400 ≤ m / (160 * Dynamic.logLogFactor N) :=
        (Nat.le_div_iff_mul_le (by positivity)).mpr (by linarith)
      unfold tMinWhp
      exact hdiv.trans (le_max_right 2 _)
    have hL2 := two_le_slabScale N
    have hL12_ge : 4096 ≤ slabScale N ^ 12 := by
      calc 4096 = 2 ^ 12 := by decide
        _ ≤ slabScale N ^ 12 := Nat.pow_le_pow_left hL2 12
    have hdiv_s : 32 * slabScale N ^ 12 / (tMinWhp N - 1) ≤ slabScale N ^ 12 / 10 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      set q10 := slabScale N ^ 12 / 10
      set r10 := slabScale N ^ 12 % 10
      have h10 : 10 * q10 + r10 = slabScale N ^ 12 := Nat.div_add_mod _ 10
      have hr10 : r10 < 10 := Nat.mod_lt _ (by decide : 0 < 10)
      set t1 := tMinWhp N - 1
      have ht1 : 399 ≤ t1 := by omega
      have ht2 : tMinWhp N - 1 - 1 = t1 - 1 := rfl
      rw [ht2, ← h10]
      have hmul399 : 399 * q10 ≤ t1 * q10 := Nat.mul_le_mul_right q10 ht1
      omega
    have h3s : 3 * nSliceWhp N ≤ slabScale N ^ 12 := by
      unfold nSliceWhp
      have h1 : slabScale N ^ 12 / 10 * 10 ≤ slabScale N ^ 12 := Nat.div_mul_le_self _ 10
      omega
    calc totalBTreeNodesWhp N
        = numBucketsWhp N * (3 * nSliceWhp N) := by unfold totalBTreeNodesWhp; ring
      _ ≤ numBucketsWhp N * slabScale N ^ 12 := Nat.mul_le_mul_left _ h3s
      _ ≤ N := numBucketsWhp_mul_scale_pow12_le hth
  have htc_le : maxTrieNodesWhp c N * 2 ^ bCharWhp N ≤ N :=
    (Nat.le_mul_of_pos_right _ hptr_pos).trans htc
  have htm_le : 6 * maxTrieNodesWhp c N ≤ N :=
    (Nat.le_mul_of_pos_right _ hptr_pos).trans htm
  have htl_le : 6 * qEpochWhp N + 6 ≤ N :=
    (Nat.le_mul_of_pos_right _ hptr_pos).trans htl
  have hbm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hn4 := four_le_of_whpThreshold_le hth
  have hm_ge22 : 2 ^ 22 ≤ Nat.log 2 N := (by decide : 2 ^ 22 ≤ 6553600).trans (hbmin.trans hbm)
  have h16pg_le : 16 * pageSizeWhp N ≤ N := by
    have hlt1 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
    have hpow1 : 2 ≤ 2 ^ (Nat.log 2 N + 1) :=
      (by decide : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hcl_n2 : Nat.clog 2 (N + 2) ≤ Nat.log 2 N + 2 := by
      refine (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr ?_
      rw [Nat.pow_succ]; omega
    have hpg_le : pageSizeWhp N ≤ Nat.log 2 N + 2 := max_le (by omega) hcl_n2
    calc 16 * pageSizeWhp N
        ≤ 16 * (Nat.log 2 N + 2) := Nat.mul_le_mul_left 16 hpg_le
      _ ≤ 64000 * ((Nat.log 2 N - 22) + 22 + 2) := by omega
      _ ≤ 2 ^ ((Nat.log 2 N - 22) + 22) := mul_64000_le_two_pow _
      _ = 2 ^ Nat.log 2 N := by congr 1; omega
      _ ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
  have hN_ge_big : 2 ^ 100 ≤ N := by
    calc 2 ^ 100 ≤ 2 ^ (Nat.log 2 N) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
  have hpg_dir_le : 4 * (N / pageSizeWhp N + 4) ≤ N := by
    have hpg32 : 32 ≤ pageSizeWhp N := le_max_left 32 _
    have hdiv : N / pageSizeWhp N ≤ N / 32 := Nat.div_le_div_left hpg32 (by decide)
    have hmul32 : N / 32 * 32 ≤ N := Nat.div_mul_le_self N 32
    have h2_100 : 1024 ≤ 2 ^ 100 := by decide
    omega
  have hslab_dir_le : 4 * (N / slabSizeWhp N + 4) ≤ N := by
    have hL2 := two_le_slabScale N
    have hK4 : 4 ≤ slabSizeWhp N := by
      unfold slabSizeWhp
      calc 4 = 2 ^ 2 := by decide
        _ ≤ slabScale N ^ 2 := Nat.pow_le_pow_left hL2 2
    have hL_ge : 8 ≤ slabScale N := by
      have : 3 ≤ Dynamic.logLogFactor N := by
        unfold Dynamic.logLogFactor
        rw [max_eq_left hn4]
        refine (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr ?_
        calc 2 ^ 2 = 4 := by decide
          _ < Nat.clog 2 N := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
      calc 8 = 2 ^ 3 := by decide
        _ ≤ 2 ^ Dynamic.logLogFactor N := Nat.pow_le_pow_right (by decide) this
    have hK64 : 64 ≤ slabSizeWhp N := by
      unfold slabSizeWhp
      calc 64 = 8 ^ 2 := by decide
        _ ≤ slabScale N ^ 2 := Nat.pow_le_pow_left hL_ge 2
    have hdiv : N / slabSizeWhp N ≤ N / 64 := Nat.div_le_div_left hK64 (by decide)
    have hmul64 : N / 64 * 64 ≤ N := Nat.div_mul_le_self N 64
    have h2_100 : 1024 ≤ 2 ^ 100 := by decide
    omega
  have h8MK_le : 8 * numBucketsWhp N * slabSizeWhp N ≤ N := by
    have hL2 := two_le_slabScale N
    have h8K_le : 8 * slabSizeWhp N ≤ slabScale N ^ 12 := by
      unfold slabSizeWhp
      have hp10 : 8 ≤ slabScale N ^ 10 := by
        calc 8 ≤ 2 ^ 10 := by decide
          _ ≤ slabScale N ^ 10 := Nat.pow_le_pow_left hL2 10
      calc 8 * slabScale N ^ 2 ≤ slabScale N ^ 10 * slabScale N ^ 2 :=
            Nat.mul_le_mul_right _ hp10
        _ = slabScale N ^ 12 := (Nat.pow_add _ 10 2).symm
    calc 8 * numBucketsWhp N * slabSizeWhp N
        = numBucketsWhp N * (8 * slabSizeWhp N) := by ring
      _ ≤ numBucketsWhp N * slabScale N ^ 12 := Nat.mul_le_mul_left _ h8K_le
      _ ≤ N := numBucketsWhp_mul_scale_pow12_le hth
  have h16tail_le : 16 * maxTailWhp N ≤ N := by
    have hL2 := two_le_slabScale N
    have hMK0 : 1 ≤ numBucketsWhp N := Nat.one_le_two_pow
    have hK_pos : 1 ≤ slabSizeWhp N := by
      unfold slabSizeWhp
      calc 1 ≤ 2 ^ 2 := by decide
        _ ≤ slabScale N ^ 2 := Nat.pow_le_pow_left hL2 2
    have h80K_le : 80 * slabSizeWhp N ≤ slabScale N ^ 12 := by
      unfold slabSizeWhp
      have hp10 : 80 ≤ slabScale N ^ 10 := by
        calc 80 ≤ 2 ^ 10 := by decide
          _ ≤ slabScale N ^ 10 := Nat.pow_le_pow_left hL2 10
      calc 80 * slabScale N ^ 2 ≤ slabScale N ^ 10 * slabScale N ^ 2 :=
            Nat.mul_le_mul_right _ hp10
        _ = slabScale N ^ 12 := (Nat.pow_add _ 10 2).symm
    calc 16 * maxTailWhp N
        = numBucketsWhp N * (16 * slabSizeWhp N) + 64 := by unfold maxTailWhp; ring
      _ ≤ numBucketsWhp N * (16 * slabSizeWhp N) + numBucketsWhp N * (64 * slabSizeWhp N) :=
          Nat.add_le_add_left (by nlinarith) _
      _ = numBucketsWhp N * (80 * slabSizeWhp N) := by ring
      _ ≤ numBucketsWhp N * slabScale N ^ 12 := Nat.mul_le_mul_left _ h80K_le
      _ ≤ N := numBucketsWhp_mul_scale_pow12_le hth
  refine ⟨hptr_lt, hptr_w, hlog_w, by omega, by unfold bWhp; omega,
    by unfold fpBitsWhp; omega, by unfold nodeMetaBitsWhp; omega,
    by omega, by omega, htop_le, hbot_le, hbt_le, htc_le, htm_le, htl_le,
    h16pg_le, hpg_dir_le, hslab_dir_le, h8MK_le, h16tail_le⟩

/-! ## Section 2: Stage-1 Reduced-Key, Salted Double-Tabulation, and Feistel `RealizesBounded` -/

/-- Compute limb widths and masks `((h, maskM), (maskH, (maskRem, maskTop)))` from `w₀`. -/
private def limbMasksProg : ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | w₀ => do
    let m ← pure (w₀ - 1)
    let h ← pure (m >>> 1)
    let hh ← pure (h + h)
    let maskM ← pure ((1 <<< m) - 1)
    let maskH ← pure ((1 <<< h) - 1)
    let maskRem ← pure ((1 <<< (m - h)) - 1)
    let maskTop ← pure ((1 <<< (m - hh)) - 1)
    pure ((h, maskM), (maskH, (maskRem, maskTop)))

private def LimbMasksPre (w : ℕ) : ℕ → Memory.State → Prop
  | w₀, _s => 0 < w₀ ∧ w₀ ≤ w

private theorem realizesBounded_limbMasks :
    RealizesBounded .exact limbMasksProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      LimbMasksPre (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw₀, hw₀_le⟩ := h
    dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul, Nat.shiftRight_eq_div_pow, pow_one] at *
    have hw_pos : 0 < w := lt_of_lt_of_le hw₀ hw₀_le
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hmul2 : 2 * ((d - 1) / 2) ≤ d - 1 := Nat.mul_div_le _ 2)
  all_goals try exact Nat.one_lt_two_pow hw_pos.ne'
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  all_goals omega

/-- Compute `halfMulMod (w₀ - 1) α_val (u_val &&& maskM)` from precomputed limb masks. -/
private def halfMulModBoundedProg :
    (((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) → Memory.Prog ℕ
  | (((h, maskM), (maskH, (maskRem, maskTop))), (α_val, x')) => do
    let hh ← pure (h + h)
    let α₀ ← pure (α_val &&& maskH)
    let α₁ ← pure (α_val >>> h)
    let x₀ ← pure (x' &&& maskH)
    let x₁ ← pure (x' >>> h)
    let p₀ ← pure ((α₀ * x₀) &&& maskM)
    let p₁ ← pure (((α₀ * x₁) &&& maskRem) <<< h)
    let p₂ ← pure (((α₁ * x₀) &&& maskRem) <<< h)
    let p₃ ← pure (((α₁ &&& maskTop) * (x₁ &&& maskTop)) <<< hh)
    let s₁ ← pure ((p₀ + p₁) &&& maskM)
    let s₂ ← pure ((s₁ + p₂) &&& maskM)
    pure ((s₂ + p₃) &&& maskM)

private def HalfMulModPre (w : ℕ) :
    (((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)) → Memory.State → Prop
  | (((h, maskM), (maskH, (maskRem, maskTop))), (α_val, x')), _s =>
    ∃ w₀ u_val,
      0 < w₀ ∧ w₀ ≤ w ∧ α_val < 2 ^ (w₀ - 1) ∧ u_val < 2 ^ w₀ ∧
      h = (w₀ - 1) / 2 ∧
      maskM = 2 ^ (w₀ - 1) - 1 ∧
      maskH = 2 ^ h - 1 ∧
      maskRem = 2 ^ ((w₀ - 1) - h) - 1 ∧
      maskTop = 2 ^ ((w₀ - 1) - 2 * h) - 1 ∧
      x' = u_val &&& maskM

private theorem realizesBounded_halfMulMod :
    RealizesBounded .exact halfMulModBoundedProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      HalfMulModPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨h_v, maskM⟩, ⟨maskH, ⟨maskRem, maskTop⟩⟩⟩, ⟨α_val, x'⟩⟩
    obtain ⟨w₀, u_val, hw₀, hw₀_le, hα, hu, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    dsimp only [Fits] at *
    have htwo : (w₀ - 1) / 2 + (w₀ - 1) / 2 = 2 * ((w₀ - 1) / 2) := by ring
    rw [htwo] at *
    have hpow_w : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw₀_le
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, _, _, _⟩ :=
      oddMulModWord_parts_lt hw₀ hα hu)
  all_goals try exact hp1.trans_le hpow_w
  all_goals try exact hp2.trans_le hpow_w
  all_goals try exact hp3.trans_le hpow_w
  all_goals try exact hp4.trans_le hpow_w
  all_goals try exact hp5.trans_le hpow_w
  all_goals try exact hp7.trans_le hpow_w
  all_goals try exact hp8.trans_le hpow_w
  all_goals try exact hp9.trans_le hpow_w
  all_goals try exact hp10.trans_le hpow_w
  have hle : 2 * ((w₀ - 1) / 2) ≤ w₀ - 1 := Nat.mul_div_le _ 2; omega

/-- Underflow-free subtraction `a - b` in `Memory.Prog` (`Basis.exact`). -/
def subClampProg (p : ℕ × ℕ) : Memory.Prog ℕ :=
  if p.2 < p.1 then pure (p.1 - p.2) else pure 0

theorem realizesBounded_subClamp :
    RealizesBounded .exact subClampProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  rcases d with ⟨a, b⟩; have ha := hwords 0; dsimp only [Fits] at ha ⊢; omega

@[simp] theorem clientResult_subClampProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (subClampProg (a, b)) = a - b := by
  unfold subClampProg
  split_ifs with h
  · rfl
  · simp only [prog_clientResult_pure]; omega

@[simp] private theorem runClient_state_subClampProg (x : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (subClampProg x))) = s := by
  unfold subClampProg; split_ifs <;> rfl

@[simp] theorem memoryCost_subClampProg (x : ℕ × ℕ) (s : Memory.State) :
    memoryCost (subClampProg x) s = 0 := by
  unfold subClampProg; split_ifs <;> rfl

private abbrev limbMaskM (masks : (ℕ × ℕ) × ℕ × ℕ × ℕ) : ℕ := masks.1.2

/-- Overflow-free Stage-1 `multiplyShiftReduced` computation (`0` memory ops, `¬ReadsWidth`):
given `((w₀, R_bits), (α_val, u_val))`, computes `oddMulModWord w₀ α_val u_val >>> (w₀ - R_bits)`
using only `w₀`-bit arithmetic (`< 2 ^ w₀ ≤ 2 ^ w`). -/
def oddMulReducedProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((w₀, R_bits), (α_val, u_val)) => do
    let masks ← limbMasksProg w₀
    let maskM ← pure (limbMaskM masks)
    let x' ← pure (u_val &&& maskM)
    let hm ← halfMulModBoundedProg (masks, (α_val, x'))
    let shiftR ← subClampProg (w₀, R_bits)
    pure (((u_val &&& 1) + ((((u_val >>> 1) + hm) &&& maskM) <<< 1)) >>> shiftR)

@[simp] theorem clientResult_oddMulReducedProg (w₀ R_bits α_val u_val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (oddMulReducedProg ((w₀, R_bits), (α_val, u_val))) =
      oddMulModWord w₀ α_val u_val >>> (w₀ - R_bits) := by
  have htwo : (w₀ - 1) / 2 + (w₀ - 1) / 2 = 2 * ((w₀ - 1) / 2) := by ring
  simp only [oddMulReducedProg, limbMaskM, limbMasksProg, halfMulModBoundedProg, pure_bind,
    prog_clientResult_bind, runClient_state_subClampProg, clientResult_subClampProg,
    prog_clientResult_pure, oddMulModWord, halfMulMod, Nat.shiftLeft_eq 1, one_mul,
    Nat.shiftRight_eq_div_pow _ 1, pow_one, htwo]

theorem clientState_oddMulReducedProg (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (oddMulReducedProg x) = s := by
  rcases x with ⟨⟨w₀, R_bits⟩, ⟨α_val, u_val⟩⟩
  unfold oddMulReducedProg
  simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
    limbMasksProg, halfMulModBoundedProg, prog_runClient_state_pure,
    runClient_state_subClampProg]

@[simp] theorem runClient_state_oddMulReducedProg (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    runClientState ((Memory.spec 0).runClient s (oddMulReducedProg x)) = s :=
  clientState_oddMulReducedProg x s

@[simp] theorem memoryCost_oddMulReducedProg (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (oddMulReducedProg x) s = 0 := by
  rcases x with ⟨⟨w₀, R_bits⟩, ⟨α_val, u_val⟩⟩
  unfold oddMulReducedProg limbMasksProg halfMulModBoundedProg
  simp only [pure_bind, Realization.memoryCost_bind', memoryCost_pure,
    StateTransitionSpec.clientState, memoryCost_subClampProg,
    runClient_state_subClampProg]

/-- Precondition for `oddMulReducedProg`. -/
@[expose] def OddMulReducedPre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((w₀, _R_bits), (α_val, u_val)), _s =>
    0 < w₀ ∧ w₀ ≤ w ∧ α_val < 2 ^ (w₀ - 1) ∧ u_val < 2 ^ w₀

theorem realizesBounded_oddMulReduced :
    RealizesBounded .exact oddMulReducedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      OddMulReducedPre (fun _ _ => 0) := by
  have hlm := realizesBounded_limbMasks
  have hhm := realizesBounded_halfMulMod
  have hsc := realizesBounded_subClamp
  realize
  all_goals (
    rcases d with ⟨⟨w₀, R_bits⟩, ⟨α_val, u_val⟩⟩
    obtain ⟨hw₀, hw₀_le, hα, hu⟩ := h
    try dsimp only at *
    try simp only [Nat.shiftRight_eq_div_pow _ 1, pow_one] at *
    have htwo : (w₀ - 1) / 2 + (w₀ - 1) / 2 = 2 * ((w₀ - 1) / 2) := by ring
    simp only [limbMasksProg, halfMulModBoundedProg, pure_bind, prog_clientResult_pure,
      StateTransitionSpec.clientState, prog_runClient_state_pure,
      Nat.shiftLeft_eq 1, one_mul, Nat.shiftRight_eq_div_pow _ 1, pow_one, htwo] at *
    have hw_pos : 0 < w := lt_of_lt_of_le hw₀ hw₀_le
    have hpow_w : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw₀_le
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hp11, _, hp13⟩ :=
      oddMulModWord_parts_lt hw₀ hα hu)
  all_goals try exact ⟨hw₀, hw₀_le⟩
  all_goals try exact ⟨w₀, u_val, hw₀, hw₀_le, hα, hu, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try exact Nat.one_lt_two_pow hw_pos.ne'
  all_goals try exact hp11.trans_le hpow_w
  exact hp13.trans_le hpow_w

/-- Context `((hashBase, wVal), (c_tab, b_char))` paired with `j` for the inner double-tabulation
character loop. -/
private abbrev DtInnerCtx := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- Inner-loop state `((i, y_acc), r_cur)`. -/
private abbrev DtInnerAcc := (ℕ × ℕ) × ℕ

private def dtInnerStepProg : DtInnerCtx × DtInnerAcc → Memory.Prog DtInnerAcc
  | ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y_acc), r_cur)) => do
    let powB ← pure (1 <<< b_char)
    let maskB ← pure (powB - 1)
    let ch ← pure (r_cur &&& maskB)
    let row ← pure (j * (c_tab + 1) + i)
    let idx₁ ← pure (row * powB + ch)
    let t_val ← readPackedCompGenProg (((hashBase, 1), (b_char, wVal)), idx₁)
    pure ((i + 1, y_acc ^^^ t_val), r_cur >>> b_char)

private theorem memoryCost_dtInnerStepProg_pos (x : DtInnerCtx × DtInnerAcc) (s : Memory.State) :
    1 ≤ memoryCost (dtInnerStepProg x) s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩
  simp only [dtInnerStepProg, pure_bind, Realization.memoryCost_bind',
    memoryCost_readPackedCompGenProg, memoryCost_pure]
  omega

private def DtInnerStepPre (w : ℕ) : DtInnerCtx × DtInnerAcc → Memory.State → Prop
  | ((((hashBase, wVal), (c_tab, b_char)), j), ((i, y_acc), _r_cur)), s =>
    ∃ d_tab,
      0 < w ∧ w = wVal ∧ b_char < w ∧ i < c_tab ∧ j < d_tab ∧
      c_tab + 1 < 2 ^ w ∧
      BitPackedDoubleTabulation.topEntries c_tab d_tab b_char < 2 ^ w ∧
      y_acc < 2 ^ b_char ∧
      hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤ s.frontier

private theorem mul_le_topEntries (c_tab d_tab b_char : ℕ) :
    d_tab * (c_tab + 1) ≤ BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
  calc d_tab * (c_tab + 1) = (c_tab + 1) * d_tab := Nat.mul_comm _ _
    _ ≤ (c_tab + 1) * d_tab * 2 ^ b_char := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow

private theorem realizesBounded_dtInnerStep :
    RealizesBounded .exact dtInnerStepProg
      (WordEncoding.encode (α := DtInnerCtx × DtInnerAcc))
      (WordEncoding.encode (α := DtInnerAcc))
      DtInnerStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨hashBase, wVal⟩, ⟨c_tab, b_char⟩⟩, j⟩, ⟨⟨i, y_acc⟩, r_cur⟩⟩
    obtain ⟨d_tab, hw, hwVal, hbc, hi, hj, hc1, htop_lt, hy, hfr⟩ := h
    subst hwVal
    try dsimp only at *
    try simp only [Nat.shiftLeft_eq 1, one_mul, clientResult_readPackedCompGenProg] at *
    have hpow_lt : 2 ^ b_char < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have hch_lt : r_cur &&& (2 ^ b_char - 1) < 2 ^ b_char := by
      rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hrow_lt : j * (c_tab + 1) + i < d_tab * (c_tab + 1) := by
      calc j * (c_tab + 1) + i
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
    have hidx_lt : (j * (c_tab + 1) + i) * 2 ^ b_char + (r_cur &&& (2 ^ b_char - 1)) <
        BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
      calc (j * (c_tab + 1) + i) * 2 ^ b_char + (r_cur &&& (2 ^ b_char - 1))
          < (j * (c_tab + 1) + i) * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hch_lt _
        _ = (j * (c_tab + 1) + i + 1) * 2 ^ b_char := by ring
        _ ≤ (d_tab * (c_tab + 1)) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow_lt
        _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
            unfold BitPackedDoubleTabulation.topEntries; ring)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_lt
  all_goals try exact Nat.one_lt_two_pow hw.ne'
  all_goals try exact hc1
  all_goals try exact (hrow_lt.trans_le (mul_le_topEntries ..)).trans htop_lt
  all_goals try exact hidx_lt.trans htop_lt
  all_goals try exact ⟨BitPackedDoubleTabulation.topEntries c_tab d_tab b_char,
    hw, rfl, hbc.le, hidx_lt, hfr⟩
  all_goals try exact (by omega : i + 1 < c_tab + 1).trans hc1
  exact (Nat.xor_lt_two_pow hy (readPacked_lt ..)).trans hpow_lt

private def dtInnerLoopProg : (DtInnerCtx × DtInnerAcc) × ℕ → Memory.Prog DtInnerAcc
  | ((ctx, st), n) => iterate dtInnerStepProg ctx n st

private theorem realizesBounded_dtInnerLoop :
    RealizesBounded .exact dtInnerLoopProg
      (WordEncoding.encode (α := (DtInnerCtx × DtInnerAcc) × ℕ))
      (WordEncoding.encode (α := DtInnerAcc))
      (fun w ((ctx, st), n) s => iterationSafe dtInnerStepProg DtInnerStepPre w ctx n st s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := DtInnerCtx))
    (WordEncoding.encode (α := DtInnerAcc))
    realizesBounded_dtInnerStep
    memoryCost_dtInnerStepProg_pos

/-- Context `(((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, rKey)))` for the
outer double-tabulation loop. -/
private abbrev DtOuterCtx := (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)))

private def dtOuterStepProg : DtOuterCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, rKey)))), (j, out_acc)) =>
    do
      let powB ← pure (1 <<< b_char)
      let z0 ← pure 0
      let innerRes ← dtInnerLoopProg
        (((((hashBase, wVal), (c_tab, b_char)), j), ((z0, z0), rKey)), c_tab)
      let (_iFin, y_acc) ← pure innerRes.1
      let row_s ← pure (j * (c_tab + 1) + c_tab)
      let idx_s ← pure (row_s * powB + s_val)
      let t_salt ← readPackedCompGenProg (((hashBase, 1), (b_char, wVal)), idx_s)
      let y_j ← pure (y_acc ^^^ t_salt)
      let idx₂ ← pure (j * powB + y_j)
      let z_j ← readPackedCompGenProg (((hashBase, offBot_v), (M_out, wVal)), idx₂)
      pure (j + 1, out_acc ^^^ z_j)

private theorem memoryCost_dtOuterStepProg_pos (x : DtOuterCtx × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (dtOuterStepProg x) s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold dtOuterStepProg
  simp only [pure_bind, Realization.memoryCost_bind', memoryCost_readPackedCompGenProg,
    memoryCost_pure]
  omega

private theorem dtInnerLoop_inv {hashBase w c_tab d_tab b_char j : ℕ} {s : Memory.State}
    (hw : 0 < w) (hbc : b_char < w) (hj : j < d_tab) (hc1 : c_tab + 1 < 2 ^ w)
    (htop_lt : BitPackedDoubleTabulation.topEntries c_tab d_tab b_char < 2 ^ w)
    (hfr : hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤ s.frontier) :
    ∀ m i y r, i + m ≤ c_tab → y < 2 ^ b_char →
      let ctx : DtInnerCtx := (((hashBase, w), (c_tab, b_char)), j)
      iterationSafe dtInnerStepProg DtInnerStepPre w ctx m ((i, y), r) s ∧
      (Memory.spec 0).clientState s (iterate dtInnerStepProg ctx m ((i, y), r)) = s ∧
      memoryCost (iterate dtInnerStepProg ctx m ((i, y), r)) s = 2 * m ∧
      (((Memory.spec 0).clientResult s (iterate dtInnerStepProg ctx m ((i, y), r))).1).2 <
        2 ^ b_char := by
  intro m
  induction m with
  | zero =>
    intro i y r _ hy
    exact ⟨trivial, rfl, by simp [iterate], hy⟩
  | succ m ih =>
    intro i y r him hy
    set ctx : DtInnerCtx := (((hashBase, w), (c_tab, b_char)), j)
    have hpre : DtInnerStepPre w (ctx, ((i, y), r)) s :=
      ⟨d_tab, hw, rfl, hbc, by omega, hj, hc1, htop_lt, hy, hfr⟩
    have hst1 : (Memory.spec 0).clientState s (dtInnerStepProg (ctx, ((i, y), r))) = s := by
      unfold dtInnerStepProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
      rfl
    have hc1_cost : memoryCost (dtInnerStepProg (ctx, ((i, y), r))) s = 2 := by
      simp [dtInnerStepProg, ctx]
    set y_next := y ^^^ readPacked (hashBase + 1) b_char w s.mem
      ((j * (c_tab + 1) + i) * (1 <<< b_char) + (r &&& ((1 <<< b_char) - 1)))
    have hres1 : (Memory.spec 0).clientResult s (dtInnerStepProg (ctx, ((i, y), r))) =
        ((i + 1, y_next), r >>> b_char) := by
      simp [dtInnerStepProg, ctx, y_next]
    have hy_next : y_next < 2 ^ b_char :=
      Nat.xor_lt_two_pow hy (readPacked_lt ..)
    obtain ⟨hs_m, hst_m, hcost_m, hy_m⟩ := ih (i + 1) y_next (r >>> b_char) (by omega) hy_next
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold iterationSafe
      rw [clientResult_width, clientState_width, hst1, hres1]
      exact ⟨hpre, hs_m⟩
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst_m]
    · unfold iterate
      rw [Realization.memoryCost_bind', hc1_cost, hst1, hres1, hcost_m]
      ring
    · unfold iterate
      rw [StateTransitionSpec.clientResult_bind, hst1, hres1]
      exact hy_m

private def DtOuterStepPre (w : ℕ) : DtOuterCtx × (ℕ × ℕ) → Memory.State → Prop
  | (((((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, _rKey)))), (j, out_acc)),
    s =>
    ∃ d_tab,
      0 < w ∧ w = wVal ∧ b_char < w ∧ M_out ≤ w ∧
      offBot_v = BitPackedDoubleTabulation.offBot w c_tab d_tab b_char ∧
      s_val < 2 ^ b_char ∧ j < d_tab ∧ d_tab < 2 ^ w ∧ c_tab + 1 < 2 ^ w ∧
      out_acc < 2 ^ M_out ∧
      BitPackedDoubleTabulation.topEntries c_tab d_tab b_char < 2 ^ w ∧
      BitPackedDoubleTabulation.botEntries d_tab b_char < 2 ^ w ∧
      hashBase + BitPackedDoubleTabulation.space w c_tab d_tab b_char M_out ≤ s.frontier

private theorem realizesBounded_dtOuterStep :
    RealizesBounded .exact dtOuterStepProg
      (WordEncoding.encode (α := DtOuterCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      DtOuterStepPre (fun _ _ => 0) := by
  have hil := realizesBounded_dtInnerLoop
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, c_tab⟩⟩, ⟨⟨b_char, M_out⟩, ⟨s_val, rKey⟩⟩⟩,
      ⟨j, out_acc⟩⟩
    obtain ⟨d_tab, hw, hwVal, hbc, hM, hoff, hs_lt, hj, hd_lt, hc1, hout_lt, htop_lt, hbot_lt,
      hfr⟩ := h
    subst hwVal; subst hoff
    dsimp only at *
    try simp only [Nat.shiftLeft_eq 1, one_mul, dtInnerLoopProg, StateTransitionSpec.clientState,
      clientResult_readPackedCompGenProg, runClient_state_readPackedCompGenProg] at *
    have hfr_top : hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤
        s.frontier := by unfold BitPackedDoubleTabulation.space at hfr; omega
    have hfr_bot : hashBase + BitPackedDoubleTabulation.offBot w c_tab d_tab b_char +
        BitPackedDoubleTabulation.botWords w d_tab b_char M_out ≤ s.frontier := by
      unfold BitPackedDoubleTabulation.space at hfr
      unfold BitPackedDoubleTabulation.offBot
      omega
    obtain ⟨hsafe_in, hst_in, _, hy_in⟩ :=
      dtInnerLoop_inv hw hbc hj hc1 htop_lt hfr_top c_tab 0 0 rKey (by omega)
        (Nat.two_pow_pos b_char)
    dsimp only [StateTransitionSpec.clientState] at hst_in hy_in
    rw [hst_in] at *
    have hpow_lt : 2 ^ b_char < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbc
    have hrow_s : j * (c_tab + 1) + c_tab < d_tab * (c_tab + 1) := by
      calc j * (c_tab + 1) + c_tab
          < j * (c_tab + 1) + (c_tab + 1) := Nat.add_lt_add_left (by omega) _
        _ = (j + 1) * (c_tab + 1) := by ring
        _ ≤ d_tab * (c_tab + 1) := Nat.mul_le_mul_right _ hj
    have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
        BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
      calc (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val
          < (j * (c_tab + 1) + c_tab) * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hs_lt _
        _ = (j * (c_tab + 1) + c_tab + 1) * 2 ^ b_char := by ring
        _ ≤ (d_tab * (c_tab + 1)) * 2 ^ b_char := Nat.mul_le_mul_right _ hrow_s
        _ = BitPackedDoubleTabulation.topEntries c_tab d_tab b_char := by
            unfold BitPackedDoubleTabulation.topEntries; ring
    set y_in_v := (((Memory.spec 0).clientResult s (iterate dtInnerStepProg
      ((((hashBase, w), (c_tab, b_char)), j)) c_tab ((0, 0), rKey))).1).2
    have hyj_lt : y_in_v ^^^ readPacked (hashBase + 1) b_char w s.mem
        ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val) < 2 ^ b_char :=
      Nat.xor_lt_two_pow hy_in (readPacked_lt ..)
    have hidx2_lt : j * 2 ^ b_char + (y_in_v ^^^ readPacked (hashBase + 1) b_char w s.mem
        ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val)) <
        BitPackedDoubleTabulation.botEntries d_tab b_char := by
      calc _ < j * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hyj_lt _
        _ = (j + 1) * 2 ^ b_char := by ring
        _ ≤ d_tab * 2 ^ b_char := Nat.mul_le_mul_right _ hj)
  all_goals try exact hpow_lt
  all_goals try exact hsafe_in
  all_goals try exact hc1
  all_goals try exact Nat.one_lt_two_pow hw.ne'
  all_goals try exact (hrow_s.trans_le (mul_le_topEntries ..)).trans htop_lt
  all_goals try exact hidx_s.trans htop_lt
  all_goals try exact ⟨BitPackedDoubleTabulation.topEntries c_tab d_tab b_char,
    hw, rfl, hbc.le, hidx_s, hfr_top⟩
  all_goals try exact hyj_lt.trans hpow_lt
  all_goals try exact hidx2_lt.trans hbot_lt
  all_goals try exact ⟨BitPackedDoubleTabulation.botEntries d_tab b_char,
    hw, rfl, hM, hidx2_lt, hfr_bot⟩
  all_goals try exact (by omega : j + 1 ≤ d_tab).trans_lt hd_lt
  exact ((Nat.xor_lt_two_pow hout_lt (readPacked_lt ..)).trans_le
    (Nat.pow_le_pow_right (by decide) hM))

private def dtOuterLoopProg : (DtOuterCtx × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((ctx, st), n) => iterate dtOuterStepProg ctx n st

private theorem realizesBounded_dtOuterLoop :
    RealizesBounded .exact dtOuterLoopProg
      (WordEncoding.encode (α := (DtOuterCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ctx, st), n) s => iterationSafe dtOuterStepProg DtOuterStepPre w ctx n st s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := DtOuterCtx))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizesBounded_dtOuterStep
    memoryCost_dtOuterStepProg_pos

/-- Input tuple `(((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, M_out))))
× (s_val, u_val)` for `evalSaltedBoundedProg`. -/
abbrev SaltedHashInput :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) × (ℕ × ℕ)

/-- Parameter-free `RealizesBounded .exact` salted bit-packed double-tabulation evaluator
(`¬ReadsWidth`, `1 + 2 * d_tab * (c_tab + 2)` memory reads). -/
def evalSaltedBoundedProg : SaltedHashInput → Memory.Prog ℕ
  | (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, M_out))))),
     (s_val, u_val)) => do
    let α_val ← Memory.read hashBase
    let rKey ← oddMulReducedProg ((w₀, R_bits), (α_val, u_val))
    let z0 ← pure 0
    let out ← dtOuterLoopProg
      ((((((hashBase, offBot_v), (wVal, c_tab)), ((b_char, M_out), (s_val, rKey)))), (z0, z0)),
        d_tab)
    pure out.2

private theorem dtOuterLoop_inv {hashBase w c_tab d_tab b_char M_out s_val rKey : ℕ}
    {s : Memory.State} (hw : 0 < w) (hbc : b_char < w) (hM : M_out ≤ w) (hs_lt : s_val < 2 ^ b_char)
    (hd_lt : d_tab < 2 ^ w) (hc1 : c_tab + 1 < 2 ^ w)
    (htop_lt : BitPackedDoubleTabulation.topEntries c_tab d_tab b_char < 2 ^ w)
    (hbot_lt : BitPackedDoubleTabulation.botEntries d_tab b_char < 2 ^ w)
    (hfr : hashBase + BitPackedDoubleTabulation.space w c_tab d_tab b_char M_out ≤ s.frontier) :
    let offBot_v := BitPackedDoubleTabulation.offBot w c_tab d_tab b_char
    let ctx : DtOuterCtx := (((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (s_val, rKey)))
    ∀ m j out, j + m ≤ d_tab → out < 2 ^ M_out →
      iterationSafe dtOuterStepProg DtOuterStepPre w ctx m (j, out) s ∧
      (Memory.spec 0).clientState s (iterate dtOuterStepProg ctx m (j, out)) = s ∧
      memoryCost (iterate dtOuterStepProg ctx m (j, out)) s = 2 * m * (c_tab + 2) := by
  intro offBot_v ctx m
  induction m with
  | zero =>
    intro j out _ _
    exact ⟨trivial, rfl, by simp [iterate]⟩
  | succ m ih =>
    intro j out hjm hout
    have hj : j < d_tab := by omega
    have hpre : DtOuterStepPre w (ctx, (j, out)) s :=
      ⟨d_tab, hw, rfl, hbc, hM, rfl, hs_lt, hj, hd_lt, hc1, hout, htop_lt, hbot_lt, hfr⟩
    have hfr_top : hashBase + 1 + BitPackedDoubleTabulation.topWords w c_tab d_tab b_char ≤
        s.frontier := by unfold BitPackedDoubleTabulation.space at hfr; omega
    obtain ⟨_, hst_in, hcost_in, _⟩ :=
      dtInnerLoop_inv hw hbc hj hc1 htop_lt hfr_top c_tab 0 0 rKey (by omega)
        (Nat.two_pow_pos b_char)
    have hst1 : (Memory.spec 0).clientState s (dtOuterStepProg (ctx, (j, out))) = s := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hst_in]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
      rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
      rfl
    have hc1_cost : memoryCost (dtOuterStepProg (ctx, (j, out))) s = 2 * (c_tab + 2) := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind, Realization.memoryCost_bind', hcost_in, hst_in,
        memoryCost_readPackedCompGenProg, runClient_state_readPackedCompGenProg, memoryCost_pure]
      ring
    have hfst1 : ((Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out)))).1 = j + 1 := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [prog_clientResult_bind, hst_in]
      simp only [prog_clientResult_bind, runClient_state_readPackedCompGenProg,
        prog_clientResult_pure]
    have hsnd1 : ((Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out)))).2 <
        2 ^ M_out := by
      unfold dtOuterStepProg dtInnerLoopProg
      dsimp only [ctx]
      simp only [pure_bind]
      rw [prog_clientResult_bind, hst_in]
      simp only [prog_clientResult_bind, runClient_state_readPackedCompGenProg,
        clientResult_readPackedCompGenProg, prog_clientResult_pure]
      exact Nat.xor_lt_two_pow hout (readPacked_lt ..)
    obtain ⟨hs_m, hst_m, hcost_m⟩ :=
      ih (j + 1) (((Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out)))).2)
        (by omega) hsnd1
    have hp_eq : (j + 1, ((Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out)))).2) =
        (Memory.spec 0).clientResult s (dtOuterStepProg (ctx, (j, out))) :=
      Prod.ext hfst1.symm rfl
    rw [hp_eq] at hs_m hst_m hcost_m
    refine ⟨?_, ?_, ?_⟩
    · unfold iterationSafe
      rw [clientResult_width, clientState_width, hst1]
      exact ⟨hpre, hs_m⟩
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hst1, hst_m]
    · unfold iterate
      rw [Realization.memoryCost_bind', hc1_cost, hst1, hcost_m]
      ring

/-- Precondition for `evalSaltedBoundedProg`. -/
@[expose] def EvalSaltedBoundedPre (w : ℕ) : SaltedHashInput → Memory.State → Prop
  | (((((hashBase, offBot_v), (wVal, w₀)), ((_R_bits, c_tab), (d_tab, (b_char, M_out))))),
     (s_val, u_val)), s =>
    0 < w ∧ w = wVal ∧ 0 < w₀ ∧ w₀ ≤ w ∧ b_char < w ∧ M_out ≤ w ∧
    offBot_v = BitPackedDoubleTabulation.offBot w c_tab d_tab b_char ∧
    s.mem hashBase < 2 ^ (w₀ - 1) ∧
    s_val < 2 ^ b_char ∧ u_val < 2 ^ w₀ ∧
    d_tab < 2 ^ w ∧ c_tab + 1 < 2 ^ w ∧
    BitPackedDoubleTabulation.topEntries c_tab d_tab b_char < 2 ^ w ∧
    BitPackedDoubleTabulation.botEntries d_tab b_char < 2 ^ w ∧
    hashBase + BitPackedDoubleTabulation.space w c_tab d_tab b_char M_out ≤ s.frontier

theorem realizesBounded_evalSaltedBounded :
    RealizesBounded .exact evalSaltedBoundedProg
      (WordEncoding.encode (α := SaltedHashInput))
      (WordEncoding.encode (α := ℕ))
      EvalSaltedBoundedPre (fun _ _ => 0) := by
  have hom := realizesBounded_oddMulReduced
  have hol := realizesBounded_dtOuterLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
      ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, M_out⟩⟩⟩⟩, ⟨s_val, u_val⟩⟩
    obtain ⟨hw, hwVal, hw₀, hw₀_le, hbc, hM, hoff, hα, hs_lt, hu_lt, hd_lt, hc1,
      htop_lt, hbot_lt, hfr⟩ := h
    subst hwVal; subst hoff
    dsimp only at *
    have hsp_pos := BitPackedDoubleTabulation.space_pos w c_tab d_tab b_char M_out
    obtain ⟨hsafe_out, _, _⟩ :=
      dtOuterLoop_inv (rKey := oddMulModWord w₀ (s.mem hashBase) u_val >>> (w₀ - R_bits))
        hw hbc hM hs_lt hd_lt hc1 htop_lt hbot_lt hfr d_tab 0 0 (by omega) (Nat.two_pow_pos M_out))
  all_goals try exact ⟨hw₀, hw₀_le, hα, hu_lt⟩
  simpa only [StateTransitionSpec.clientState, runClient_state_oddMulReducedProg,
    clientResult_oddMulReducedProg, prog_clientResult_pure, prog_runClient_state_pure] using
    hsafe_out

/-- Exact functional agreement between `evalSaltedBoundedProg` and
`BitPackedDoubleTabulation.evalSalted`, proved by simulation against
`BitPackedDoubleTabulation.evalProg_spec` without duplicating prefix-XOR lemmas. -/
theorem evalSaltedBoundedProg_eq_evalSalted {U w w₀ R_bits c_tab d_tab b_char M_out s_max
    hashBase : ℕ} {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d_tab b_char M_out}
    {s : Memory.State} (hw₀ : 0 < w₀) (hs_max : s_max ≤ 2 ^ b_char)
    (hrep : BitPackedDoubleTabulation.SeedRep hashBase w w₀ c_tab d_tab b_char M_out θ s.mem)
    (salt : Fin s_max) (u : Fin U) :
    let offBot_v := BitPackedDoubleTabulation.offBot w c_tab d_tab b_char
    let inp : SaltedHashInput :=
      (((((hashBase, offBot_v), (w, w₀)), ((R_bits, c_tab), (d_tab, (b_char, M_out))))),
        (salt.val, u.val))
    (Memory.spec 0).clientResult s (evalSaltedBoundedProg inp) =
      (BitPackedDoubleTabulation.evalSalted U w₀ R_bits c_tab d_tab b_char M_out s_max θ
        (salt, u)).val ∧
    (Memory.spec 0).clientState s (evalSaltedBoundedProg inp) = s ∧
    memoryCost (evalSaltedBoundedProg inp) s = 1 + 2 * d_tab * (c_tab + 2) := by
  intro offBot_v inp
  let hp := BitPackedDoubleTabulation.mkHashParams w w₀ R_bits c_tab d_tab b_char M_out
  have hin_eq : ∀ j m st,
      (Memory.spec 0).clientResult s
        (iterate dtInnerStepProg (((hashBase, w), (c_tab, b_char)), j) m st) =
        (Memory.spec 0).clientResult s
          (iterate BitPackedDoubleTabulation.innerStepGenProg (hp, (hashBase, j)) m st) ∧
      (Memory.spec 0).clientState s
        (iterate dtInnerStepProg (((hashBase, w), (c_tab, b_char)), j) m st) = s ∧
      (Memory.spec 0).clientState s
        (iterate BitPackedDoubleTabulation.innerStepGenProg (hp, (hashBase, j)) m st) = s ∧
      memoryCost (iterate dtInnerStepProg (((hashBase, w), (c_tab, b_char)), j) m st) s =
        2 * m := by
    intro j m
    induction m with
    | zero => intro st; exact ⟨rfl, rfl, rfl, rfl⟩
    | succ m ih =>
      intro ⟨⟨i, y⟩, r⟩
      have hst1 : (Memory.spec 0).clientState s
          (dtInnerStepProg ((((hashBase, w), (c_tab, b_char)), j), ((i, y), r))) = s := by
        unfold dtInnerStepProg; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]; rfl
      have hst2 : (Memory.spec 0).clientState s
          (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hashBase, j)), ((i, y), r))) = s := rfl
      have hres_step : (Memory.spec 0).clientResult s
          (dtInnerStepProg ((((hashBase, w), (c_tab, b_char)), j), ((i, y), r))) =
          (Memory.spec 0).clientResult s
            (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hashBase, j)), ((i, y), r))) := by
        unfold dtInnerStepProg BitPackedDoubleTabulation.innerStepGenProg readPackedGenProg
        simp only [hp, pure_bind, Nat.shiftLeft_eq 1, one_mul,
          BitPackedDoubleTabulation.hpMaskB_mk, BitPackedDoubleTabulation.hpCPlusOne_mk,
          BitPackedDoubleTabulation.hpPowB_mk, BitPackedDoubleTabulation.hpBChar_mk,
          BitPackedDoubleTabulation.hpW_mk, prog_clientResult_bind,
          clientResult_readPackedCompGenProg, runClient_state_readPackedCompGenProg,
          clientResult_readPackedProg, prog_clientResult_pure]
      have hc1 : memoryCost
          (dtInnerStepProg ((((hashBase, w), (c_tab, b_char)), j), ((i, y), r))) s = 2 := by
        simp [dtInnerStepProg]
      obtain ⟨hrm, hs1m, hs2m, hcm⟩ := ih
        ((Memory.spec 0).clientResult s
          (dtInnerStepProg ((((hashBase, w), (c_tab, b_char)), j), ((i, y), r))))
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold iterate
        rw [prog_clientResult_bind, prog_clientResult_bind, hst1, hst2, ← hres_step, hrm]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hs1m]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst2, ← hres_step, hs2m]
      · unfold iterate; rw [Realization.memoryCost_bind', hc1, hst1, hcm]; ring
  have hout_eq : ∀ rKey m st,
      (Memory.spec 0).clientResult s
        (iterate dtOuterStepProg
          (((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))) m st) =
        (Memory.spec 0).clientResult s
          (iterate BitPackedDoubleTabulation.outerStepGenProg
            (hp, (hashBase, (salt.val, rKey))) m st) ∧
      (Memory.spec 0).clientState s
        (iterate dtOuterStepProg
          (((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))) m st) = s ∧
      (Memory.spec 0).clientState s
        (iterate BitPackedDoubleTabulation.outerStepGenProg
          (hp, (hashBase, (salt.val, rKey))) m st) = s ∧
      memoryCost (iterate dtOuterStepProg
        (((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))) m st) s =
        2 * m * (c_tab + 2) := by
    intro rKey m
    induction m with
    | zero =>
      intro st
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp [iterate]
    | succ m ih =>
      intro ⟨j, out⟩
      obtain ⟨hr_in, hs1_in, hs2_in, hc_in⟩ := hin_eq j c_tab ((0, 0), rKey)
      have hst1 : (Memory.spec 0).clientState s
          (dtOuterStepProg
            ((((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))),
              (j, out))) = s := by
        unfold dtOuterStepProg dtInnerLoopProg; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hs1_in]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
        rfl
      have hst2 : (Memory.spec 0).clientState s
          (BitPackedDoubleTabulation.outerStepGenProg
            ((hp, (hashBase, (salt.val, rKey))), (j, out))) = s := by
        unfold BitPackedDoubleTabulation.outerStepGenProg BitPackedDoubleTabulation.innerLoopGenProg
          readPackedGenProg
        simp only [hp, pure_bind, BitPackedDoubleTabulation.hpCTab_mk]
        rw [StateTransitionSpec.clientState_bind, hs2_in]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedProg]
        rw [StateTransitionSpec.clientState_bind, clientState_readPackedProg]
        rfl
      have hres_step : (Memory.spec 0).clientResult s
          (dtOuterStepProg
            ((((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))),
              (j, out))) =
          (Memory.spec 0).clientResult s
            (BitPackedDoubleTabulation.outerStepGenProg
              ((hp, (hashBase, (salt.val, rKey))), (j, out))) := by
        unfold dtOuterStepProg dtInnerLoopProg BitPackedDoubleTabulation.outerStepGenProg
          BitPackedDoubleTabulation.innerLoopGenProg readPackedGenProg
        simp only [hp, pure_bind, Nat.shiftLeft_eq 1, one_mul,
          BitPackedDoubleTabulation.hpCTab_mk, BitPackedDoubleTabulation.hpCPlusOne_mk,
          BitPackedDoubleTabulation.hpPowB_mk, BitPackedDoubleTabulation.hpBChar_mk,
          BitPackedDoubleTabulation.hpW_mk, BitPackedDoubleTabulation.hpOffBot_mk,
          BitPackedDoubleTabulation.hpMOut_mk]
        rw [prog_clientResult_bind, hs1_in]
        conv_rhs => rw [prog_clientResult_bind, hs2_in, ← hr_in]
        simp only [prog_clientResult_bind, clientResult_readPackedCompGenProg,
          runClient_state_readPackedCompGenProg, clientResult_readPackedProg,
          prog_clientResult_pure, offBot_v]
        rfl
      have hc1 : memoryCost
          (dtOuterStepProg
            ((((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))),
              (j, out))) s = 2 * (c_tab + 2) := by
        unfold dtOuterStepProg dtInnerLoopProg
        simp only [pure_bind, Realization.memoryCost_bind', hc_in, hs1_in,
          memoryCost_readPackedCompGenProg, runClient_state_readPackedCompGenProg, memoryCost_pure]
        ring
      obtain ⟨hrm, hs1m, hs2m, hcm⟩ := ih
        ((Memory.spec 0).clientResult s
          (dtOuterStepProg
            ((((hashBase, offBot_v), (w, c_tab)), ((b_char, M_out), (salt.val, rKey))),
              (j, out))))
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold iterate
        rw [prog_clientResult_bind, prog_clientResult_bind, hst1, hst2, ← hres_step, hrm]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hs1m]
      · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst2, ← hres_step, hs2m]
      · unfold iterate; rw [Realization.memoryCost_bind', hc1, hst1, hcm]; ring
  set rKey := oddMulModWord w₀ (s.mem hashBase) u.val >>> (w₀ - R_bits)
  obtain ⟨hr_out, hs1_out, _, hc_out⟩ := hout_eq rKey d_tab (0, 0)
  have href := BitPackedDoubleTabulation.evalProg_spec hw₀ hs_max hrep salt u (R := R_bits)
  have hread_st : (Memory.spec 0).clientState s (Memory.read hashBase) = s := rfl
  have hodd_st := clientState_oddMulReducedProg ((w₀, R_bits), (s.mem hashBase, u.val)) s
  have heval_eq : (Memory.spec 0).clientResult s
      (BitPackedDoubleTabulation.evalProg w w₀ R_bits c_tab d_tab b_char M_out
        ((hashBase, salt.val), u.val)) =
      ((Memory.spec 0).clientResult s
        (iterate BitPackedDoubleTabulation.outerStepGenProg
          (hp, (hashBase, (salt.val, rKey))) d_tab (0, 0))).2 := by
    unfold BitPackedDoubleTabulation.evalProg BitPackedDoubleTabulation.evalGenProg
      BitPackedDoubleTabulation.outerLoopGenProg
    simp only [pure_bind, BitPackedDoubleTabulation.hpMaskM_mk,
      BitPackedDoubleTabulation.hpMaskHalf_mk, BitPackedDoubleTabulation.hpHalfM_mk,
      BitPackedDoubleTabulation.hpMaskRem_mk, BitPackedDoubleTabulation.hpMaskTop_mk,
      BitPackedDoubleTabulation.hpTwoHalfM_mk, BitPackedDoubleTabulation.hpShiftR_mk,
      BitPackedDoubleTabulation.hpD_mk]
    rw [prog_clientResult_bind, hread_st, prog_clientResult_read]
    simp only [prog_clientResult_bind, prog_clientResult_pure,
      oddMulModWord, halfMulMod, rKey, hp]
  unfold evalSaltedBoundedProg dtOuterLoopProg
  dsimp only [inp]
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · rw [prog_clientResult_bind, hread_st, prog_clientResult_read,
      prog_clientResult_bind, hodd_st, clientResult_oddMulReducedProg,
      prog_clientResult_bind, hs1_out, hr_out, prog_clientResult_pure, ← heval_eq, href.1]
  · rw [StateTransitionSpec.clientState_bind, hread_st, prog_clientResult_read,
      StateTransitionSpec.clientState_bind, hodd_st, clientResult_oddMulReducedProg,
      StateTransitionSpec.clientState_bind, hs1_out]
    rfl
  · rw [Realization.memoryCost_bind', prog_memoryCost_read, hread_st, prog_clientResult_read,
      Realization.memoryCost_bind', memoryCost_oddMulReducedProg, hodd_st,
      clientResult_oddMulReducedProg, Realization.memoryCost_bind', hc_out, hs1_out,
      memoryCost_pure]
    omega

/-- Input tuple for one-round Feistel split (`(bkt, q_u)`) and inverse reconstruction (`u_rec`). -/
abbrev FeistelHashCtx := ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))

/-- Split key `u_val` into `(epochBucket, keyQuotient)` in `Memory.Prog` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def feistelSplitBoundedProg : FeistelHashCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))), u_val) =>
    do
      let powBkt ← pure (1 <<< b_bits)
      let maskBkt ← pure (powBkt - 1)
      let q_u ← pure (u_val >>> b_bits)
      let low_u ← pure (u_val &&& maskBkt)
      let z0 ← pure 0
      let h_q ← evalSaltedBoundedProg
        (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
          (z0, q_u))
      let bkt ← pure ((h_q &&& maskBkt) ^^^ low_u)
      pure (bkt, q_u)

/-- Precondition for `feistelSplitBoundedProg`. -/
@[expose] def FeistelSplitPre (w : ℕ) : FeistelHashCtx × ℕ → Memory.State → Prop
  | (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))), u_val),
    s =>
    b_bits < w ∧ u_val < 2 ^ w₀ ∧
    EvalSaltedBoundedPre w
      (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
        (0, u_val >>> b_bits)) s

theorem realizesBounded_feistelSplit :
    RealizesBounded .exact feistelSplitBoundedProg
      (WordEncoding.encode (α := FeistelHashCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      FeistelSplitPre (fun _ _ => 0) := by
  have hes := realizesBounded_evalSaltedBounded
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
      ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, b_bits⟩⟩⟩⟩, u_val⟩
    obtain ⟨hbb, hu_lt, hpre⟩ := h
    have hwVal : w = wVal := hpre.2.1
    subst hwVal
    dsimp only at *
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *
    have hpow_b : 2 ^ b_bits < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbb)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_b
  all_goals try exact hpre
  refine (Nat.xor_lt_two_pow ?_ ?_).trans hpow_b <;>
    (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))

theorem feistelSplitBoundedProg_spec {c U w N hashBase : ℕ}
    {θ_bkt : BktSeed c U N} {s : Memory.State}
    (hnU : N ≤ U)
    (hrep : BitPackedDoubleTabulation.SeedRep hashBase w (redWidthWhp U)
      (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) θ_bkt s.mem)
    (u : Fin U) :
    let offBot_v := BitPackedDoubleTabulation.offBot w (cTabWhp c) (dTabWhp c) (bCharWhp N)
    let ctx : FeistelHashCtx :=
      (((hashBase, offBot_v), (w, redWidthWhp U)),
        ((redBitsWhp c N, cTabWhp c), (dTabWhp c, (bCharWhp N, bWhp N))))
    (Memory.spec 0).clientResult s (feistelSplitBoundedProg (ctx, u.val)) =
      (epochBucket c U N θ_bkt u, keyQuotient (bWhp N) u.val) ∧
    (Memory.spec 0).clientState s (feistelSplitBoundedProg (ctx, u.val)) = s ∧
    memoryCost (feistelSplitBoundedProg (ctx, u.val)) s =
      1 + 2 * dTabWhp c * (cTabWhp c + 2) := by
  intro offBot_v ctx
  have hq_lt := keyQuotient_bWhp_lt hnU u
  have hev := evalSaltedBoundedProg_eq_evalSalted (U := 2 ^ quotBitsWhp U N)
    (R_bits := redBitsWhp c N) (redWidthWhp_pos U) Nat.one_le_two_pow hrep ⟨0, Nat.zero_lt_one⟩
    ⟨keyQuotient (bWhp N) u.val, hq_lt⟩
  have hq_eq : u.val >>> bWhp N = keyQuotient (bWhp N) u.val :=
    Nat.shiftRight_eq_div_pow u.val (bWhp N)
  have hlow_eq : u.val &&& ((1 <<< bWhp N) - 1) = keyLow (bWhp N) u.val := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]; rfl
  have hhb_eq : bktHash c U N θ_bkt (keyQuotient (bWhp N) u.val) =
      (BitPackedDoubleTabulation.evalSalted (2 ^ quotBitsWhp U N) (redWidthWhp U) (redBitsWhp c N)
        (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) 1 θ_bkt
        (⟨0, Nat.zero_lt_one⟩, ⟨keyQuotient (bWhp N) u.val, hq_lt⟩)).val := by
    unfold bktHash
    simp only [Nat.mod_eq_of_lt hq_lt]
  unfold feistelSplitBoundedProg
  dsimp only [ctx]
  simp only [pure_bind]
  rw [hq_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [prog_clientResult_bind, hev.2.1, hev.1, prog_clientResult_pure, hlow_eq, ← hhb_eq]
    simp only [epochBucket, feistelBucket, Nat.shiftLeft_eq 1, one_mul,
      Nat.and_two_pow_sub_one_eq_mod]
  · rw [StateTransitionSpec.clientState_bind, hev.2.1]
    rfl
  · rw [Realization.memoryCost_bind', hev.2.2, hev.2.1, memoryCost_pure, add_zero]

/-- Reconstruct key `feistelReconstruct b_bits h_bkt bkt q_val` in `Memory.Prog`
(`RealizesBounded .exact`, `¬ReadsWidth`). -/
def feistelReconBoundedProg : FeistelHashCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
     (bkt, q_val)) => do
    let powBkt ← pure (1 <<< b_bits)
    let maskBkt ← pure (powBkt - 1)
    let z0 ← pure 0
    let h_q ← evalSaltedBoundedProg
      (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
        (z0, q_val))
    let low_u ← pure ((h_q &&& maskBkt) ^^^ (bkt &&& maskBkt))
    pure ((q_val <<< b_bits) + low_u)

/-- Precondition for `feistelReconBoundedProg`. -/
@[expose] def FeistelReconPre (w : ℕ) : FeistelHashCtx × (ℕ × ℕ) → Memory.State → Prop
  | (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
     (_bkt, q_val)), s =>
    ∃ q_bits, b_bits < w ∧ q_bits + b_bits ≤ w ∧ q_val < 2 ^ q_bits ∧
      EvalSaltedBoundedPre w
        (((((hashBase, offBot_v), (wVal, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
          (0, q_val)) s

theorem realizesBounded_feistelRecon :
    RealizesBounded .exact feistelReconBoundedProg
      (WordEncoding.encode (α := FeistelHashCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      FeistelReconPre (fun _ _ => 0) := by
  have hes := realizesBounded_evalSaltedBounded
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
      ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, b_bits⟩⟩⟩⟩, ⟨bkt, q_val⟩⟩
    obtain ⟨q_bits, hbb, hqb_w, hq_lt, hpre⟩ := h
    have hwVal : w = wVal := hpre.2.1
    subst hwVal
    dsimp only at *
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *
    have hpow_b : 2 ^ b_bits < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hbb
    have hsh_lt : q_val <<< b_bits < 2 ^ w := by
      rw [Nat.shiftLeft_eq]
      calc q_val * 2 ^ b_bits < 2 ^ q_bits * 2 ^ b_bits :=
            Nat.mul_lt_mul_of_pos_right hq_lt (Nat.two_pow_pos _)
        _ = 2 ^ (q_bits + b_bits) := (Nat.pow_add 2 _ _).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hqb_w)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_b
  all_goals try exact hpre
  all_goals try (
    refine (Nat.xor_lt_two_pow ?_ ?_).trans hpow_b <;>
      (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
  set low := ((Memory.spec 0).clientResult s
    (evalSaltedBoundedProg
      (((((hashBase, offBot_v), (w, w₀)), ((R_bits, c_tab), (d_tab, (b_char, b_bits))))),
        (0, q_val))) &&& (2 ^ b_bits - 1)) ^^^ (bkt &&& (2 ^ b_bits - 1))
  have hlow_lt : low < 2 ^ b_bits := by
    refine Nat.xor_lt_two_pow ?_ ?_ <;>
      (rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [Nat.shiftLeft_eq]
  calc q_val * 2 ^ b_bits + low
      < q_val * 2 ^ b_bits + 2 ^ b_bits := Nat.add_lt_add_left hlow_lt _
    _ = (q_val + 1) * 2 ^ b_bits := by ring
    _ ≤ 2 ^ q_bits * 2 ^ b_bits := Nat.mul_le_mul_right _ hq_lt
    _ = 2 ^ (q_bits + b_bits) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hqb_w

theorem feistelReconBoundedProg_spec {c U w N hashBase bkt q_val : ℕ}
    {θ_bkt : BktSeed c U N} {s : Memory.State}
    (hq_lt : q_val < 2 ^ quotBitsWhp U N)
    (hrep : BitPackedDoubleTabulation.SeedRep hashBase w (redWidthWhp U)
      (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) θ_bkt s.mem) :
    let offBot_v := BitPackedDoubleTabulation.offBot w (cTabWhp c) (dTabWhp c) (bCharWhp N)
    let ctx : FeistelHashCtx :=
      (((hashBase, offBot_v), (w, redWidthWhp U)),
        ((redBitsWhp c N, cTabWhp c), (dTabWhp c, (bCharWhp N, bWhp N))))
    (Memory.spec 0).clientResult s (feistelReconBoundedProg (ctx, (bkt, q_val))) =
      feistelReconstruct (bWhp N) (bktHash c U N θ_bkt) bkt q_val ∧
    (Memory.spec 0).clientState s (feistelReconBoundedProg (ctx, (bkt, q_val))) = s ∧
    memoryCost (feistelReconBoundedProg (ctx, (bkt, q_val))) s =
      1 + 2 * dTabWhp c * (cTabWhp c + 2) := by
  intro offBot_v ctx
  have hev := evalSaltedBoundedProg_eq_evalSalted (U := 2 ^ quotBitsWhp U N)
    (R_bits := redBitsWhp c N) (redWidthWhp_pos U) Nat.one_le_two_pow hrep ⟨0, Nat.zero_lt_one⟩
    ⟨q_val, hq_lt⟩
  have hhb_eq : bktHash c U N θ_bkt q_val =
      (BitPackedDoubleTabulation.evalSalted (2 ^ quotBitsWhp U N) (redWidthWhp U) (redBitsWhp c N)
        (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) 1 θ_bkt
        (⟨0, Nat.zero_lt_one⟩, ⟨q_val, hq_lt⟩)).val := by
    unfold bktHash; simp only [Nat.mod_eq_of_lt hq_lt]
  unfold feistelReconBoundedProg
  dsimp only [ctx]
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · rw [prog_clientResult_bind, hev.2.1, hev.1, prog_clientResult_pure, ← hhb_eq]
    simp only [feistelReconstruct, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
  · rw [StateTransitionSpec.clientState_bind, hev.2.1]
    rfl
  · rw [Realization.memoryCost_bind', hev.2.2, hev.2.1, memoryCost_pure, add_zero]

/-- Unconditional state preservation of `evalSaltedBoundedProg` (all memory operations are reads).
-/
theorem clientState_evalSaltedBoundedProg (inp : SaltedHashInput) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalSaltedBoundedProg inp) = s := by
  rcases inp with ⟨⟨⟨⟨hashBase, offBot_v⟩, ⟨wVal, w₀⟩⟩,
    ⟨⟨R_bits, c_tab⟩, ⟨d_tab, ⟨b_char, M_out⟩⟩⟩⟩, ⟨s_val, u_val⟩⟩
  have hin : ∀ c_in k st, (Memory.spec 0).clientState s (iterate dtInnerStepProg c_in k st) = s :=
    fun c_in k => by
      rcases c_in with ⟨⟨⟨hb, wv⟩, ⟨ct, bc⟩⟩, j⟩
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro ⟨⟨i, y⟩, r⟩; unfold iterate
        rw [StateTransitionSpec.clientState_bind]
        have hs1 : (Memory.spec 0).clientState s
            (dtInnerStepProg ((((hb, wv), (ct, bc)), j), ((i, y), r))) = s := by
          unfold dtInnerStepProg; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
          rfl
        rw [hs1]; exact ih _
  have hout : ∀ c_out k st,
      (Memory.spec 0).clientState s (iterate dtOuterStepProg c_out k st) = s :=
    fun c_out k => by
      rcases c_out with ⟨⟨⟨hb, ob⟩, ⟨wv, ct⟩⟩, ⟨⟨bc, mo⟩, ⟨sv, rk⟩⟩⟩
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro ⟨j, out⟩; unfold iterate
        rw [StateTransitionSpec.clientState_bind]
        have hs1 : (Memory.spec 0).clientState s
            (dtOuterStepProg (((((hb, ob), (wv, ct)), ((bc, mo), (sv, rk)))), (j, out))) = s := by
          unfold dtOuterStepProg dtInnerLoopProg; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, hin,
            StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg,
            StateTransitionSpec.clientState_bind, clientState_readPackedCompGenProg]
          rfl
        rw [hs1]; exact ih _
  unfold evalSaltedBoundedProg dtOuterLoopProg; simp only [pure_bind]
  have hr : (Memory.spec 0).clientState s (Memory.read hashBase) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr,
    StateTransitionSpec.clientState_bind, clientState_oddMulReducedProg,
    StateTransitionSpec.clientState_bind, hout]
  rfl

/-- Unconditional state preservation of `feistelSplitBoundedProg`. -/
theorem clientState_feistelSplitBoundedProg (x : FeistelHashCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (feistelSplitBoundedProg x) = s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, _⟩
  unfold feistelSplitBoundedProg; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]
  rfl

/-- Unconditional state preservation of `feistelReconBoundedProg`. -/
theorem clientState_feistelReconBoundedProg (x : FeistelHashCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (feistelReconBoundedProg x) = s := by
  rcases x with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, ⟨_, _⟩⟩
  unfold feistelReconBoundedProg; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_evalSaltedBoundedProg]
  rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
