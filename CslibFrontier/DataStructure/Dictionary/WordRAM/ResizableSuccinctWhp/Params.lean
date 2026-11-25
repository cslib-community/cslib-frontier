/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpParams
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild
import CslibFrontier.Foundations.Data.Nat.ChooseLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameters and Strict `1 · OPT` Dual-Epoch Space Accounting for Resizable WHP SOSA 2024

This module defines the memory-layout offsets, per-epoch metadata budgets, and shared item-slot
widths for the deamortized worst-case with-high-probability resizable succinct dynamic dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]),
building on the `1 · OPT` dual-epoch space-accounting framework of
`CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild` and proving that both
resting and intermediate dual-epoch hardware frontiers stay strictly within `1 · OPT`:
`Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t` words
(`OPT(U, V, n_t) + O_c(n_t log log n_t) + O(w)` bits—never `2 · OPT`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.rootHdrWhp`, `slabSizeWhp`,
  `maxSlabsPerBktWhp`, `maxTailWhp`, `pageSizeWhp`: root header and slab/tail/page parameters.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.epochMetaWordsWhp`,
  `epochItemBitsWhp`, `dualEpochLayoutWordsWhp`: per-epoch metadata word count, dense item slot
  bit-width, and full dual-epoch word footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.whpResizableSpaceFactor`,
  `whpResizableSpaceConst`: `c`-only `1 · OPT` succinct space constants.

## Main results

* `epochMetaWordsWhp_le_bits`: bit-packed ceiling bound on `epochMetaWordsWhp c w N` across all
  `whpThreshold c ≤ N`.
* `epochSafe_metaWords_le`: under `EpochCapSafe (whpThreshold c) U N n_t`, metadata words of epoch
  `N` are bounded by `O_c(n_t * Dynamic.logLogFactor n_t) / w`.
* `epochSafe_itemBits_le_optBits`: under `EpochCapSafe (whpThreshold c) U N n_t`, `n_t`
  shared item slots of width `max w_src w_dst` use at most
  `Dynamic.optBits U V n_t + O_c(n_t * Dynamic.logLogFactor n_t)` bits.
* `dualEpochLayoutWordsWhp_le_succinctWords`: master `1 · OPT` dual-epoch word-space theorem across
  all four `(N_src, N_dst)` combinations (`(0, 0)`, `(0, N_dst)`, `(N_src, N_dst)`, `(N_src, 0)`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Section 1: Header, Slab, Tail, Page, and Epoch Metadata Parameters -/

/-- Root control header size (`192` words) storing universe bounds `U - 1`, `V - 1`, `w`, `keyBits`,
`valBits`, live item counts, 12-phase dual-epoch rebuild control words, small-epoch 2-word headers,
and two 64-word `EpochParamTable` blocks (`[base + 64, base + 192)`). -/
@[expose] def rootHdrWhp : ℕ := 192

/-- Dynamic full-slab item count `L ^ 2 = (slabScale N) ^ 2` for hashed epoch capacity `N`. -/
@[expose] def slabSizeWhp (N : ℕ) : ℕ :=
  (slabScale N) ^ 2

/-- Maximum full slabs owned by a single bucket `4 * (slabScale N) ^ 10` (`capMaxWhp N / L^2`). -/
@[expose] def maxSlabsPerBktWhp (N : ℕ) : ℕ :=
  4 * (slabScale N) ^ 10

/-- Maximum total partial-tail items across all `M` buckets (`M * L^2 + 4`). -/
@[expose] def maxTailWhp (N : ℕ) : ℕ :=
  numBucketsWhp N * slabSizeWhp N + 4

/-- Shared arena page size `max 32 (Nat.clog 2 (N + 2))` for `PagePairState` (`O(N)` page bits). -/
@[expose] def pageSizeWhp (N : ℕ) : ℕ :=
  max 32 (Nat.clog 2 (N + 2))

/-- Total metadata words `M(N)` of an epoch of capacity `N` (`0` in the small regime
`N < whpThreshold c`; Stage-2 salted bucket & fingerprint double-tabulation tables, dynamic `L^2`
slab & circular-tail directories, 3-role SWAR B+-tree slices, dual `BufTrie`s, and `PagePairState`
directory when `whpThreshold c ≤ N`). -/
@[expose] def epochMetaWordsWhp (c w N : ℕ) : ℕ :=
  if N < whpThreshold c then
    0
  else
    let M := numBucketsWhp N
    let ptrB := globalPtrBits N
    let pgB := pageSizeWhp N
    32 +
    BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) +
    BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) +
    packedWords (16 * M) ptrB w +
    packedWords (M * maxSlabsPerBktWhp N) ptrB w +
    packedWords (8 * M * slabSizeWhp N) ptrB w +
    packedWords (4 * (N / slabSizeWhp N + 4)) ptrB w +
    packedWords (16 * maxTailWhp N) ptrB w +
    packedWords (totalBTreeNodesWhp N) (nodeMetaBitsWhp N) w +
    packedWords (totalBTreeNodesWhp N) (keysWordBitsWhp N) w +
    packedWords (totalBTreeNodesWhp N) (valsWordBitsWhp N) w +
    2 * packedWords (maxTrieNodesWhp c N * 2 ^ bCharWhp N) ptrB w +
    2 * packedWords (6 * maxTrieNodesWhp c N) ptrB w +
    2 * packedWords (6 * qEpochWhp N + 6) ptrB w +
    packedWords (4 * (N / pgB + 4)) ptrB w +
    packedWords (16 * pgB) ptrB w

/-- Per-item bit-width `w_epoch(N)` in the dense item arena: `keyBits U + valBits V` in the small
regime (`N < whpThreshold c`) and `quotBitsWhp U N + valBits V` in the large regime
(`whpThreshold c ≤ N`). -/
@[expose] def epochItemBitsWhp (c U V N : ℕ) : ℕ :=
  if N < whpThreshold c then
    keyBits U + valBits V
  else
    quotBitsWhp U N + valBits V

/-- Full dual-epoch word footprint `rootHdrWhp + M(N_src) + M(N_dst) + 4 + packedWords n_t w_slot w`
where `w_slot = max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst)`. -/
@[expose] def dualEpochLayoutWordsWhp (c U V w N_src N_dst n_t : ℕ) : ℕ :=
  rootHdrWhp + epochMetaWordsWhp c w N_src + epochMetaWordsWhp c w N_dst + 4 +
    packedWords n_t (max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst)) w

/-- `c`-only redundancy multiplier on `n_t * Dynamic.logLogFactor n_t` covering both resting and
dual-epoch migration states (`12 * whpSpaceFactor c + 960000`). -/
@[expose] def whpResizableSpaceFactor (c : ℕ) : ℕ :=
  12 * whpSpaceFactor c + 960000

/-- Universal additive `w`-bit word slack (`1024` words, independent of `c, U, V, w, n_t`). -/
@[expose] def whpResizableSpaceConst : ℕ := 1024

/-- Machine-state component of a `(result, state, history)` `StateTransitionSpec.runClient`
output triple. -/
abbrev clientOutState {α σ η : Type} (out : α × σ × η) : σ := out.2.1

/-! ## Section 2: Metadata Bit Bounds and `1 · OPT` Dual-Epoch Space Proofs -/

theorem whpThreshold_ge_64 (c : ℕ) : 64 ≤ whpThreshold c := by
  have hb := le_bMinWhp c
  calc 64 = 2 ^ 6 := by decide
    _ ≤ 2 ^ bMinWhp c := Nat.pow_le_pow_right (by decide) (by omega)
    _ = whpThreshold c := (whpThreshold_eq c).symm

private theorem ceil_div_add_le (A c₁ B c₂ w : ℕ) :
    ((A + w - 1) / w + c₁) + ((B + w - 1) / w + c₂) ≤
      (A + B + w - 1) / w + (c₁ + c₂ + 1) := by
  have h := div_add_packedWords_le A c₁ B 1 w
  unfold packedWords at h
  rw [Nat.mul_one] at h
  omega

private theorem clog_sq_le_of_whpThreshold {c N : ℕ} (hth : whpThreshold c ≤ N) :
    (pageSizeWhp N) ^ 2 ≤ N := by
  have hbm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hN4 := four_le_of_whpThreshold_le hth
  set m := Nat.log 2 N
  have hlt : N + 2 ≤ 2 ^ (m + 2) := by
    have h1 : N < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
    rw [Nat.pow_succ]
    omega
  have hcl : Nat.clog 2 (N + 2) ≤ m + 2 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hlt
  have hpg : pageSizeWhp N ≤ m + 2 := by
    unfold pageSizeWhp
    exact max_le (by omega) hcl
  have hpow_lin : ∀ x : ℕ, 2 * x + 37 ≤ 2 ^ (x + 16) := by
    intro x
    induction x with
    | zero => decide
    | succ x ihx =>
      have h1 : 1 ≤ 2 ^ (x + 16) := Nat.one_le_two_pow
      rw [show x + 1 + 16 = (x + 16) + 1 by omega, Nat.pow_succ]
      omega
  have hsq_pow : ∀ k : ℕ, 16 ≤ k → (k + 2) ^ 2 ≤ 2 ^ k := by
    intro k hk
    obtain ⟨d, rfl⟩ : ∃ d, k = d + 16 := ⟨k - 16, by omega⟩
    induction d with
    | zero => decide
    | succ d ih =>
      calc (d + 1 + 16 + 2) ^ 2
          = (d + 16 + 2) ^ 2 + (2 * d + 37) := by ring
        _ ≤ 2 ^ (d + 16) + 2 ^ (d + 16) := Nat.add_le_add (ih (by omega)) (hpow_lin d)
        _ = 2 ^ (d + 1 + 16) := by
            rw [show d + 1 + 16 = (d + 16) + 1 by omega, Nat.pow_succ]; ring
  calc (pageSizeWhp N) ^ 2
      ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left hpg 2
    _ ≤ 2 ^ m := hsq_pow m (by omega)
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

/-- Upper bound on `epochMetaWordsWhp c w N` in terms of bit count `60000 * N * logLogFactor N`
plus constant word overhead (`120` words), valid for every `N : ℕ` and `w : ℕ`. -/
theorem epochMetaWordsWhp_le_bits (c w N : ℕ) :
    epochMetaWordsWhp c w N ≤
      (60000 * N * Dynamic.logLogFactor N + w - 1) / w + 120 := by
  unfold epochMetaWordsWhp
  split_ifs with hsmall
  · exact Nat.zero_le _
  · have hth : whpThreshold c ≤ N := Nat.le_of_not_lt hsmall
    obtain ⟨htb1, htb2, htb3, htc, htm, htl⟩ := sublinear_table_bits_le hth
    have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
    have hell := Dynamic.one_le_logLogFactor N
    have hL2 := two_le_slabScale N
    have hpg_sq := clog_sq_le_of_whpThreshold hth
    set ell := Dynamic.logLogFactor N
    set L := slabScale N
    set M := numBucketsWhp N
    set ptrB := globalPtrBits N
    set pgB := pageSizeWhp N
    have hptr : ptrB ≤ 2 * L := by
      have hb : 0 < bucketBits N := by
        have hbm := bMinWhp_le_log hth
        have hbmin := le_bMinWhp c
        have h4 := four_le_of_whpThreshold_le hth
        have hcl : Nat.log 2 N ≤ Nat.clog 2 N := Nat.log_le_clog 2 N
        have h320 : 320 * ell ≤ bCharWhp N :=
          (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
        unfold bCharWhp at h320
        unfold bucketBits
        omega
      exact globalPtrBits_le_two_mul_slabScale hb
    have hne : N ≤ N * ell := Nat.le_mul_of_pos_right _ hell
    have hML_le : M * L ≤ N := by
      have hL11 : 1 ≤ L ^ 11 := Nat.one_le_pow 11 L (by omega)
      calc M * L ≤ M * L * L ^ 11 := Nat.le_mul_of_pos_right _ hL11
        _ = M * L ^ 12 := by ring
        _ ≤ N := hM_L12
    have hML3_le : M * L ^ 3 ≤ N := by
      have hL9 : 1 ≤ L ^ 9 := Nat.one_le_pow 9 L (by omega)
      calc M * L ^ 3 ≤ M * L ^ 3 * L ^ 9 := Nat.le_mul_of_pos_right _ hL9
        _ = M * L ^ 12 := by ring
        _ ≤ N := hM_L12
    have hML11_le : M * L ^ 11 ≤ N := by
      calc M * L ^ 11 ≤ M * L ^ 11 * L := Nat.le_mul_of_pos_right _ (by omega)
        _ = M * L ^ 12 := by ring
        _ ≤ N := hM_L12
    have hb1 : (16 * M) * ptrB ≤ 32 * (N * ell) := by
      calc (16 * M) * ptrB ≤ (16 * M) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 32 * (M * L) := by ring
        _ ≤ 32 * N := Nat.mul_le_mul_left 32 hML_le
        _ ≤ 32 * (N * ell) := Nat.mul_le_mul_left 32 hne
    have hb2 : (M * maxSlabsPerBktWhp N) * ptrB ≤ 8 * (N * ell) := by
      calc (M * (4 * L ^ 10)) * ptrB ≤ (M * (4 * L ^ 10)) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 8 * (M * L ^ 11) := by ring
        _ ≤ 8 * N := Nat.mul_le_mul_left 8 hML11_le
        _ ≤ 8 * (N * ell) := Nat.mul_le_mul_left 8 hne
    have hb3 : (8 * M * slabSizeWhp N) * ptrB ≤ 16 * (N * ell) := by
      calc (8 * M * L ^ 2) * ptrB ≤ (8 * M * L ^ 2) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 16 * (M * L ^ 3) := by ring
        _ ≤ 16 * N := Nat.mul_le_mul_left 16 hML3_le
        _ ≤ 16 * (N * ell) := Nat.mul_le_mul_left 16 hne
    have hdiv_L2 : N / slabSizeWhp N * L ≤ N := by
      have hLL : L ≤ L ^ 2 := by
        rw [sq]
        exact Nat.le_mul_of_pos_right L (by omega)
      calc N / L ^ 2 * L ≤ N / L ^ 2 * L ^ 2 := Nat.mul_le_mul_left _ hLL
        _ ≤ N := Nat.div_mul_le_self N (L ^ 2)
    have hL_le_N : 128 * L ≤ N := by
      have hM1 : 1 ≤ M := by unfold M numBucketsWhp; exact Nat.one_le_two_pow
      have h128 : 128 ≤ L ^ 11 := by
        calc 128 ≤ 2 ^ 11 := by decide
          _ ≤ L ^ 11 := Nat.pow_le_pow_left hL2 11
      calc 128 * L ≤ L ^ 11 * L := Nat.mul_le_mul_right L h128
        _ = 1 * L ^ 12 := by ring
        _ ≤ M * L ^ 12 := Nat.mul_le_mul_right _ hM1
        _ ≤ N := hM_L12
    have hb4 : (4 * (N / slabSizeWhp N + 4)) * ptrB ≤ 10 * (N * ell) := by
      calc (4 * (N / slabSizeWhp N + 4)) * ptrB
          ≤ (4 * (N / slabSizeWhp N + 4)) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 8 * (N / slabSizeWhp N * L) + 32 * L := by ring
        _ ≤ 8 * N + N := Nat.add_le_add (Nat.mul_le_mul_left 8 hdiv_L2) (by omega)
        _ ≤ 10 * (N * ell) := by linarith
    have hb5 : (16 * maxTailWhp N) * ptrB ≤ 40 * (N * ell) := by
      calc (16 * (M * L ^ 2 + 4)) * ptrB
          ≤ (16 * (M * L ^ 2 + 4)) * (2 * L) := Nat.mul_le_mul_left _ hptr
        _ = 32 * (M * L ^ 3) + 128 * L := by ring
        _ ≤ 32 * N + N := Nat.add_le_add (Nat.mul_le_mul_left 32 hML3_le) hL_le_N
        _ ≤ 40 * (N * ell) := by linarith
    have h8t : 8 ≤ tMinWhp N := by
      have h320 : 320 * ell ≤ bCharWhp N :=
        (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
      unfold bCharWhp at h320
      have hdiv : 8 ≤ Nat.log 2 N / (160 * ell) :=
        (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
      unfold tMinWhp
      exact hdiv.trans (le_max_right 2 _)
    have hnslice_mul : nSliceWhp N * tMinWhp N ≤ 128 * L ^ 12 := by
      have h1 : 32 * L ^ 12 / (tMinWhp N - 1) * (tMinWhp N - 1) ≤ 32 * L ^ 12 :=
        Nat.div_mul_le_self _ _
      have h2 : tMinWhp N ≤ 2 * (tMinWhp N - 1) := by omega
      have h3 : 32 * L ^ 12 / (tMinWhp N - 1) * tMinWhp N ≤ 64 * L ^ 12 := by
        calc 32 * L ^ 12 / (tMinWhp N - 1) * tMinWhp N
            ≤ 32 * L ^ 12 / (tMinWhp N - 1) * (2 * (tMinWhp N - 1)) :=
              Nat.mul_le_mul_left _ h2
          _ = 2 * (32 * L ^ 12 / (tMinWhp N - 1) * (tMinWhp N - 1)) := by ring
          _ ≤ 64 * L ^ 12 := by linarith
      have h64_t : 64 * tMinWhp N ≤ 64 * L ^ 12 := by
        refine Nat.mul_le_mul_left 64 ((tMinWhp_le_slabScale N).trans ?_)
        exact Nat.le_self_pow (by decide) L
      unfold nSliceWhp
      rw [Nat.add_mul]
      dsimp only [L] at h3 h64_t ⊢
      calc _ ≤ 64 * slabScale N ^ 12 + 64 * slabScale N ^ 12 := Nat.add_le_add h3 h64_t
        _ = 128 * slabScale N ^ 12 := by ring
    have htot_t : totalBTreeNodesWhp N * tMinWhp N ≤ 384 * N := by
      calc (3 * M * nSliceWhp N) * tMinWhp N
          = (3 * M) * (nSliceWhp N * tMinWhp N) := by ring
        _ ≤ (3 * M) * (128 * L ^ 12) := Nat.mul_le_mul_left (3 * M) hnslice_mul
        _ = 384 * (M * L ^ 12) := by ring
        _ ≤ 384 * N := Nat.mul_le_mul_left 384 hM_L12
    have hb_bt_meta : totalBTreeNodesWhp N * nodeMetaBitsWhp N ≤ 384 * (N * ell) := by
      have hm_le : nodeMetaBitsWhp N ≤ tMinWhp N * ell := by
        have h4 : 4 ≤ 4 * ell := Nat.le_mul_of_pos_right 4 hell
        have h5 : 5 * ell ≤ tMinWhp N * ell := Nat.mul_le_mul_right ell (by omega)
        unfold nodeMetaBitsWhp
        dsimp only [ell] at h4 h5 ⊢
        omega
      calc totalBTreeNodesWhp N * nodeMetaBitsWhp N
          ≤ totalBTreeNodesWhp N * (tMinWhp N * ell) := Nat.mul_le_mul_left _ hm_le
        _ = (totalBTreeNodesWhp N * tMinWhp N) * ell := by ring
        _ ≤ (384 * N) * ell := Nat.mul_le_mul_right ell htot_t
        _ = 384 * (N * ell) := by ring
    have hb_bt_keys : totalBTreeNodesWhp N * keysWordBitsWhp N ≤ 29184 * (N * ell) := by
      have hk_le : keysWordBitsWhp N ≤ 76 * (tMinWhp N * ell) := by
        have hk1 : keyLaneBitsWhp N ≤ 38 * ell := by
          unfold keyLaneBitsWhp fpBitsWhp
          dsimp only [ell] at hell ⊢
          omega
        calc 2 * tMinWhp N * keyLaneBitsWhp N
            ≤ 2 * tMinWhp N * (38 * ell) := Nat.mul_le_mul_left _ hk1
          _ = 76 * (tMinWhp N * ell) := by ring
      calc totalBTreeNodesWhp N * keysWordBitsWhp N
          ≤ totalBTreeNodesWhp N * (76 * (tMinWhp N * ell)) := Nat.mul_le_mul_left _ hk_le
        _ = 76 * (totalBTreeNodesWhp N * tMinWhp N) * ell := by ring
        _ ≤ 76 * (384 * N) * ell := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 76 htot_t)
        _ = 29184 * (N * ell) := by ring
    have hb_bt_vals : totalBTreeNodesWhp N * valsWordBitsWhp N ≤ 15360 * (N * ell) := by
      have hv_le : valsWordBitsWhp N ≤ 40 * (tMinWhp N * ell) := by
        have hv1 : valLaneBitsWhp N ≤ 20 * ell := by
          unfold valLaneBitsWhp
          dsimp only [ell] at hell ⊢
          omega
        calc 2 * tMinWhp N * valLaneBitsWhp N
            ≤ 2 * tMinWhp N * (20 * ell) := Nat.mul_le_mul_left _ hv1
          _ = 40 * (tMinWhp N * ell) := by ring
      calc totalBTreeNodesWhp N * valsWordBitsWhp N
          ≤ totalBTreeNodesWhp N * (40 * (tMinWhp N * ell)) := Nat.mul_le_mul_left _ hv_le
        _ = 40 * (totalBTreeNodesWhp N * tMinWhp N) * ell := by ring
        _ ≤ 40 * (384 * N) * ell := Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 40 htot_t)
        _ = 15360 * (N * ell) := by ring
    have hpg8 : 8 ≤ pgB := (by decide : 8 ≤ 32).trans (le_max_left 32 _)
    have hptr_le_pg : ptrB ≤ pgB := by
      unfold ptrB globalPtrBits pgB pageSizeWhp
      exact (Nat.clog_mono_right 2 (by omega)).trans (le_max_right 32 _)
    have hb_pg1 : (4 * (N / pgB + 4)) * ptrB ≤ 24 * (N * ell) := by
      have h1 : ptrB ≤ 2 * pgB := by omega
      have h2 : N / pgB * pgB ≤ N := Nat.div_mul_le_self N pgB
      have h32 : 32 * pgB ≤ 16 * pgB ^ 2 := by
        rw [sq, ← mul_assoc]
        exact Nat.mul_le_mul_right pgB (by omega)
      calc (4 * (N / pgB + 4)) * ptrB
          ≤ (4 * (N / pgB + 4)) * (2 * pgB) := Nat.mul_le_mul_left _ h1
        _ = 8 * (N / pgB * pgB) + 32 * pgB := by ring
        _ ≤ 8 * N + 16 * pgB ^ 2 := Nat.add_le_add (Nat.mul_le_mul_left 8 h2) h32
        _ ≤ 8 * N + 16 * N := Nat.add_le_add_left (Nat.mul_le_mul_left 16 hpg_sq) _
        _ = 24 * N := by ring
        _ ≤ 24 * (N * ell) := Nat.mul_le_mul_left 24 hne
    have hb_pg2 : (16 * pgB) * ptrB ≤ 24 * (N * ell) := by
      calc (16 * pgB) * ptrB ≤ (16 * pgB) * pgB := Nat.mul_le_mul_left _ hptr_le_pg
        _ = 16 * pgB ^ 2 := by ring
        _ ≤ 16 * N := Nat.mul_le_mul_left 16 hpg_sq
        _ ≤ 24 * (N * ell) := by linarith
    have hsp_bkt := BitPackedDoubleTabulation.space_le w (cTabWhp c) (dTabWhp c)
      (bCharWhp N) (bWhp N)
    have hsp_fp := BitPackedDoubleTabulation.space_le w (cTabWhp c) (dTabWhp c)
      (bCharWhp N) (fpBitsWhp N)
    let B_bkt := BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp N) *
        bCharWhp N +
      BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp N) * bWhp N
    let B_fp := BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp N) *
        bCharWhp N +
      BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp N) * fpBitsWhp N
    let trieEntries := maxTrieNodesWhp c N * 2 ^ bCharWhp N
    let d1 := (16 * M) * ptrB
    let d2 := d1 + (M * maxSlabsPerBktWhp N) * ptrB
    let d3 := d2 + (8 * M * slabSizeWhp N) * ptrB
    let d4 := d3 + (4 * (N / slabSizeWhp N + 4)) * ptrB
    let d5 := d4 + (16 * maxTailWhp N) * ptrB
    let d6 := d5 + totalBTreeNodesWhp N * nodeMetaBitsWhp N
    let d7 := d6 + totalBTreeNodesWhp N * keysWordBitsWhp N
    let d8 := d7 + totalBTreeNodesWhp N * valsWordBitsWhp N
    let d9 := d8 + (2 * trieEntries) * ptrB
    let d10 := d9 + (2 * (6 * maxTrieNodesWhp c N)) * ptrB
    let d11 := d10 + (2 * (6 * qEpochWhp N + 6)) * ptrB
    let d12 := d11 + (4 * (N / pgB + 4)) * ptrB
    let B_aux := d12 + (16 * pgB) * ptrB
    have p1 := packedWords_add_le (16 * M) ptrB (M * maxSlabsPerBktWhp N) ptrB w
    have p2 := div_add_packedWords_le d2 5 (8 * M * slabSizeWhp N) ptrB w
    have p3 := div_add_packedWords_le d3 8 (4 * (N / slabSizeWhp N + 4)) ptrB w
    have p4 := div_add_packedWords_le d4 11 (16 * maxTailWhp N) ptrB w
    have p5 := div_add_packedWords_le d5 14 (totalBTreeNodesWhp N) (nodeMetaBitsWhp N) w
    have p6 := div_add_packedWords_le d6 17 (totalBTreeNodesWhp N) (keysWordBitsWhp N) w
    have p7 := div_add_packedWords_le d7 20 (totalBTreeNodesWhp N) (valsWordBitsWhp N) w
    have p8 := div_add_mul_packedWords_le 2 d8 23 trieEntries ptrB w
    have p9 := div_add_mul_packedWords_le 2 d9 29 (6 * maxTrieNodesWhp c N) ptrB w
    have p10 := div_add_mul_packedWords_le 2 d10 35 (6 * qEpochWhp N + 6) ptrB w
    have p11 := div_add_packedWords_le d11 41 (4 * (N / pgB + 4)) ptrB w
    have p12 := div_add_packedWords_le d12 44 (16 * pgB) ptrB w
    have hhash := ceil_div_add_le B_bkt 6 B_fp 6 w
    have hcomb := ceil_div_add_le (B_bkt + B_fp) 13 B_aux 47 w
    have hmul_assoc : ∀ k, (2 * k) * ptrB = 2 * (k * ptrB) := fun _ => by ring
    have htot_bits : B_bkt + B_fp + B_aux ≤ 60000 * N * Dynamic.logLogFactor N := by
      have h60k : B_bkt + B_fp + B_aux ≤ 60000 * (N * ell) := by
        dsimp only [B_bkt, B_fp, B_aux, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
        rw [hmul_assoc trieEntries, hmul_assoc (6 * maxTrieNodesWhp c N),
          hmul_assoc (6 * qEpochWhp N + 6)]
        have htc' : trieEntries * ptrB ≤ N := htc
        linarith
      calc B_bkt + B_fp + B_aux ≤ 60000 * (N * ell) := h60k
        _ = 60000 * N * Dynamic.logLogFactor N := by dsimp only [ell]; ring
    have hdiv : (B_bkt + B_fp + B_aux + w - 1) / w ≤
        (60000 * N * Dynamic.logLogFactor N + w - 1) / w :=
      Nat.div_le_div_right (by omega)
    dsimp only
    dsimp only [B_bkt, B_fp, B_aux, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1,
      trieEntries, M, ptrB, pgB, ell] at *
    omega

/-- **`c`-Independent Linear Word Bound (`epochMetaWordsWhp_le_linear`).**
Whenever `0 < w` and `bCharWhp N ≤ w` (which holds automatically whenever `N ≤ U < 2 ^ w`),
`epochMetaWordsWhp c w N ≤ 188 * N + 121` words (with constants **independent of `c`**), allowing
Phase 1 zeroing / random seed sampling and Phase 3 metadata relocation to advance at a fixed
`c`-independent rate (`O(1)` words per tick) inside a `< N / 32` operation window. -/
theorem epochMetaWordsWhp_le_linear {c w N : ℕ} (hw : 0 < w) (hbc : bCharWhp N ≤ w) :
    epochMetaWordsWhp c w N ≤ 188 * N + 121 := by
  by_cases hsmall : N < whpThreshold c
  · simp only [epochMetaWordsWhp, hsmall, ↓reduceIte]
    exact Nat.zero_le _
  · have hth : whpThreshold c ≤ N := Nat.le_of_not_lt hsmall
    have h320 : 320 * Dynamic.logLogFactor N ≤ w :=
      ((Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans
        (codeExpWhp_mul_ell_le_bCharWhp hth)).trans hbc
    have hmul : 60000 * N * Dynamic.logLogFactor N ≤ 188 * N * w := by
      calc 60000 * N * Dynamic.logLogFactor N
          ≤ 60160 * N * Dynamic.logLogFactor N := by gcongr; decide
        _ = 188 * N * (320 * Dynamic.logLogFactor N) := by ring
        _ ≤ 188 * N * w := Nat.mul_le_mul_left _ h320
    have hdiv : (60000 * N * Dynamic.logLogFactor N + w - 1) / w ≤ 188 * N + 1 := by
      rw [Nat.div_le_iff_le_mul_add_pred hw]
      have hcomm : w * (188 * N + 1) = 188 * N * w + w := by ring
      omega
    have hbits := epochMetaWordsWhp_le_bits c w N
    omega

/-- Under `EpochCapSafe (whpThreshold c) U N n_t`, the metadata bit numerator of epoch `N` is at
most `720000 * n_t * Dynamic.logLogFactor n_t`. -/
theorem epochSafe_metaWords_le {c U w N n_t : ℕ}
    (hsafe : EpochCapSafe (whpThreshold c) U N n_t) :
    epochMetaWordsWhp c w N ≤
      (720000 * n_t * Dynamic.logLogFactor n_t + w - 1) / w + 120 := by
  by_cases hN0 : N = 0
  · subst hN0
    have hlt : 0 < whpThreshold c := whpThreshold_pos c
    simp only [epochMetaWordsWhp, hlt, ↓reduceIte]
    exact Nat.zero_le _
  · simp only [EpochCapSafe, hN0, ↓reduceIte] at hsafe
    obtain ⟨_, _, hN4, _⟩ := hsafe
    have hN_le : N ≤ 4 * n_t := hN4.le
    have hell_le := Dynamic.logLogFactor_le_three_mul_of_le_four_mul hN_le
    have hmeta := epochMetaWordsWhp_le_bits c w N
    have hbits : 60000 * N * Dynamic.logLogFactor N ≤
        720000 * n_t * Dynamic.logLogFactor n_t := by
      calc 60000 * N * Dynamic.logLogFactor N
          ≤ 60000 * (4 * n_t) * (3 * Dynamic.logLogFactor n_t) := by
            gcongr
        _ = 720000 * n_t * Dynamic.logLogFactor n_t := by ring
    have hdiv : (60000 * N * Dynamic.logLogFactor N + w - 1) / w ≤
        (720000 * n_t * Dynamic.logLogFactor n_t + w - 1) / w :=
      Nat.div_le_div_right (by omega)
    omega

/-- Under `EpochCapSafe (whpThreshold c) U N n_t`, `n_t` item slots of width
`epochItemBitsWhp c U V N` use at most
`Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t` bits. -/
theorem epochSafe_itemBits_le_optBits {c U V N n_t : ℕ}
    (hsafe : EpochCapSafe (whpThreshold c) U N n_t) :
    n_t * epochItemBitsWhp c U V N ≤
      Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t := by
  have hell : 1 ≤ Dynamic.logLogFactor n_t := Dynamic.one_le_logLogFactor n_t
  by_cases hN0 : N = 0
  · subst hN0
    simp only [EpochCapSafe, ↓reduceIte] at hsafe
    obtain ⟨hlt2, hnU⟩ := hsafe
    have hlt_th : 0 < whpThreshold c := whpThreshold_pos c
    simp only [epochItemBitsWhp, hlt_th, ↓reduceIte]
    have hpow : n_t ≤ 2 ^ (bMinWhp c + 1) := by
      rw [Nat.pow_succ', ← whpThreshold_eq]
      exact hlt2.le
    have hexp : n_t * keyBits U ≤
        n_t + n_t * (bMinWhp c + 1) + Nat.clog 2 (U.choose n_t) :=
      Nat.mul_clog_le_add_clog_choose Nat.one_lt_two hnU hpow
    have hmul1 : (bMinWhp c + 48) * n_t ≤
        (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t :=
      Nat.le_mul_of_pos_right _ hell
    have hlin1 : n_t + n_t * (bMinWhp c + 1) ≤ (bMinWhp c + 48) * n_t := by
      rw [show (bMinWhp c + 48) * n_t = n_t * (bMinWhp c + 1) + 47 * n_t by ring]
      omega
    rw [Nat.mul_add]
    unfold Dynamic.optBits valBits
    omega
  · simp only [EpochCapSafe, hN0, ↓reduceIte] at hsafe
    obtain ⟨hth, hNU, hN4, hnN⟩ := hsafe
    have hnU : n_t ≤ U := hnN.trans hNU
    have hnot_lt : ¬(N < whpThreshold c) := Nat.not_lt.mpr hth
    simp only [epochItemBitsWhp, hnot_lt, ↓reduceIte]
    have hpow_N : N ≤ 2 ^ (bWhp N + 12 * Dynamic.logLogFactor N + 1) := by
      exact (Nat.lt_pow_succ_log_self Nat.one_lt_two N).le.trans
        (Nat.pow_le_pow_right (by decide) (by unfold bWhp; omega))
    have hexp : n_t * keyBits U ≤
        n_t + n_t * (bWhp N + 12 * Dynamic.logLogFactor N + 1) +
          Nat.clog 2 (U.choose n_t) :=
      Nat.mul_clog_le_add_clog_choose Nat.one_lt_two hnU (hnN.trans hpow_N)
    have hsplit : keyBits U = quotBitsWhp U N + bWhp N := (quotBitsWhp_add_bWhp hNU).symm
    rw [hsplit, Nat.mul_add] at hexp
    have hell_N := Dynamic.logLogFactor_le_three_mul_of_le_four_mul hN4.le
    have hred : n_t + n_t * (12 * Dynamic.logLogFactor N + 1) ≤
        48 * n_t * Dynamic.logLogFactor n_t := by
      calc n_t + n_t * (12 * Dynamic.logLogFactor N + 1)
          ≤ n_t + n_t * (12 * (3 * Dynamic.logLogFactor n_t) + 1) := by gcongr
        _ = 2 * n_t + 36 * (n_t * Dynamic.logLogFactor n_t) := by ring
        _ ≤ 2 * (n_t * Dynamic.logLogFactor n_t) + 36 * (n_t * Dynamic.logLogFactor n_t) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hell)) _
        _ = 38 * (n_t * Dynamic.logLogFactor n_t) := by ring
        _ ≤ 48 * n_t * Dynamic.logLogFactor n_t := by
            rw [mul_assoc 48]
            exact Nat.mul_le_mul_right _ (by decide)
    have hexp_q : n_t * quotBitsWhp U N ≤
        n_t + n_t * (12 * Dynamic.logLogFactor N + 1) + Nat.clog 2 (U.choose n_t) := by
      have hm_b : n_t * (bWhp N + 12 * Dynamic.logLogFactor N + 1) =
          n_t * bWhp N + n_t * (12 * Dynamic.logLogFactor N + 1) := by ring
      rw [hm_b] at hexp
      omega
    have hfac_le : 48 * n_t * Dynamic.logLogFactor n_t ≤
        (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left 48 _))
    rw [Nat.mul_add]
    unfold Dynamic.optBits valBits
    omega

/-- **Master `1 · OPT` Dual-Epoch Word-Space Theorem (`dualEpochLayoutWordsWhp_le_succinctWords`).**
Whenever both `N_src` and `N_dst` satisfy `EpochCapSafe (whpThreshold c) U · n_t` (covering resting
`idle` states `(N_src, 0)` as well as all active 3-phase migrations `(0, N_dst)`, `(N_src, N_dst)`,
and `(N_src, 0)`), the full dual-epoch word footprint is bounded by
`Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t` (`1 · OPT`,
never `2 · OPT`). -/
theorem dualEpochLayoutWordsWhp_le_succinctWords {c U V w N_src N_dst n_t : ℕ}
    (hsrc : EpochCapSafe (whpThreshold c) U N_src n_t)
    (hdst : EpochCapSafe (whpThreshold c) U N_dst n_t) :
    dualEpochLayoutWordsWhp c U V w N_src N_dst n_t ≤
      Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t := by
  have hm_src := epochSafe_metaWords_le (w := w) hsrc
  have hm_dst := epochSafe_metaWords_le (w := w) hdst
  have hi_src := epochSafe_itemBits_le_optBits (V := V) hsrc
  have hi_dst := epochSafe_itemBits_le_optBits (V := V) hdst
  have hmax_item :
      n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) ≤
        Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t := by
    rcases max_choice (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) with h | h <;>
      rw [h]
    · exact hi_src
    · exact hi_dst
  have hfac : 1440000 + (bMinWhp c + 48) ≤ whpResizableSpaceFactor c := by
    unfold whpResizableSpaceFactor whpSpaceFactor
    omega
  have hbits :
      720000 * n_t * Dynamic.logLogFactor n_t +
        720000 * n_t * Dynamic.logLogFactor n_t +
        n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) ≤
        Dynamic.optBits U V n_t +
          whpResizableSpaceFactor c * n_t * Dynamic.logLogFactor n_t := by
    calc 720000 * n_t * Dynamic.logLogFactor n_t +
          720000 * n_t * Dynamic.logLogFactor n_t +
          n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst)
        ≤ 720000 * n_t * Dynamic.logLogFactor n_t +
            720000 * n_t * Dynamic.logLogFactor n_t +
            (Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t) :=
          Nat.add_le_add_left hmax_item _
      _ = Dynamic.optBits U V n_t +
            (1440000 + (bMinWhp c + 48)) * n_t * Dynamic.logLogFactor n_t := by ring
      _ ≤ Dynamic.optBits U V n_t +
            whpResizableSpaceFactor c * n_t * Dynamic.logLogFactor n_t := by gcongr
  have hd := dualEpochWords_le_succinctWords
    (hdrWords := rootHdrWhp)
    (M_src := epochMetaWordsWhp c w N_src)
    (M_dst := epochMetaWordsWhp c w N_dst)
    (c_src := 120) (c_dst := 120) hm_src hm_dst hbits
  unfold whpResizableSpaceConst
  unfold dualEpochLayoutWordsWhp Dynamic.succinctWords rootHdrWhp at hd ⊢
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
