/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `1 · OPT` Migration Arena Accounting and Runtime Epoch-Parameter Computation

This module provides the arithmetic foundation and parameter-free (`¬ReadsWidth`) runtime
parameter-computation subroutines for single-tape epoch capacity migration in the resizable
succinct dynamic dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA
2024][BenderFarachColtonKuszmaulKuszmaul2024]; [Kuszmaul, Liang, and Zhou, SODA
2026][KuszmaulLiangZhou2026]):

1. **Single-tape `1 · OPT` shared item arena (`migrateArenaWords`, `migratePeakWords`):**
   Right-aligning the `n` old compacted items in a shared arena of
   `max (compactedItemWords U V w N_old n) (compactedItemWords U V w N_new n) + 6` words guarantees
   that streaming item `i` (`0 ≤ i < n`) into the growing new item prefix `[0, i + 1)` never
   overwrites unread old items `d ∈ [i + 1, n)` (`newItemEnd_le_oldItemNextWord`), while bounding
   the total migration peak footprint by `Dynamic.succinctWords 2699 888 U V w n` words
   (`migratePeakWords_le_succinctWords`, `1 · OPT` with no `2 · OPT` spike) and by `O(n)` machine
   words independent of `(U, V, w)` (`migratePeakWords_le_linear`).
2. **Overflow-free runtime `HashParams` and `CompParams` writer (`computeTargetCapProg`,
   `writeEpochParamsGenProg`):**
   `computeTargetCapProg` evaluates `targetCap U n` from `[hdrBase, hdrBase + 5)` in `≤ 1` memory
   operation, and `writeEpochParamsGenProg` populates the 8-word root header, 19-word `HashParams`
   (`mkHashParams`), and 36-word `CompParams` (`mkCompParams`) at `[dstMetaBase, dstMetaBase + 63)`
   given `N` in `O(N)` (`≤ 11 * N + 100`) operations via `RealizesBounded .exact`, without
   `Op.width` (`¬ReadsWidth`) and without arithmetic overflow even when `V = 2 ^ w` or
   `U = 2 ^ w - 1`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateArenaWords`,
  `migratePeakWords`: shared single-tape item-arena length and peak migration word footprint.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.computeTargetCapProg`,
  `writeEpochParamsGenProg`: parameter-free `Memory.Prog` evaluators for `targetCap U n` and the
  63-word active epoch parameter header `[dstMetaBase, dstMetaBase + 63)`.

## Main results

* `newItemEnd_le_oldItemNextWord`: exact word-level non-overlap between written new items `[0, j)`
  and unread right-aligned old items `[j, n)` across both growing and shrinking epochs.
* `migratePeakWords_le_succinctWords`, `w_mul_migratePeakWords_le_bits`,
  `migratePeakWords_le_linear`: `1 · OPT` succinct space bounds and `O(n)` linear word bound.
* `realizesBounded_computeTargetCap`, `computeTargetCapProg_spec`,
  `realizesBounded_writeEpochParamsGen`, `writeEpochParamsGenProg_spec`: `RealizesBounded .exact`
  certificates and functional specifications.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Single-Tape `1 · OPT` Shared Arena and Peak-Space Bounds -/

/-- Word length of the shared single-tape item arena holding both the growing prefix `[0, i)` of
new compacted items and the right-aligned suffix `[i, n)` of unread old compacted items. -/
@[expose] def migrateArenaWords (U V w N_old N_new n : ℕ) : ℕ :=
  max (compactedItemWords U V w N_old n) (compactedItemWords U V w N_new n) + 6

/-- Peak hardware word footprint above `base` during single-tape epoch capacity migration from
`(N_old, n)` to `targetCap U n`. -/
@[expose] def migratePeakWords (U V w N_old n : ℕ) : ℕ :=
  offCompItems U w N_old + offCompItems U w (targetCap U n) +
    migrateArenaWords U V w N_old (targetCap U n) n

private theorem div_ceil_le_div_add_one {a w : ℕ} (hw : 0 < w) :
    (a + w - 1) / w ≤ a / w + 1 := by
  have hle : a + w - 1 ≤ a + 1 * w := by omega
  exact (Nat.div_le_div_right hle).trans_eq (Nat.add_mul_div_right a 1 hw)

theorem div_add_div_le {a b w : ℕ} (hw : 0 < w) :
    a / w + b / w ≤ (a + b) / w := by
  have ha := Nat.mul_div_le a w
  have hb := Nat.mul_div_le b w
  exact (Nat.le_div_iff_mul_le hw).mpr (by nlinarith)

/-- **Shared-Arena Non-Overlap (`newItemEnd_le_oldItemNextWord`):**
For every `j ≤ n` (`j = i + 1` after inserting item `i`), the end word offset
`compactedItemWords U V w N_new j` of the first `j` new items is at most the word offset
`(migrateArenaWords - iwOld) + wOffQ_old j` where unread old item `j` begins, regardless of
whether `quotientBits U N_new ≤ quotientBits U N_old` (growing `N`) or
`quotientBits U N_new > quotientBits U N_old` (shrinking `N`). -/
theorem newItemEnd_le_oldItemNextWord {U V w N_old N_new n j : ℕ}
    (hw : 0 < w) (hj : j ≤ n) :
    compactedItemWords U V w N_new j ≤
      migrateArenaWords U V w N_old N_new n - compactedItemWords U V w N_old n +
        wOffQ (quotientBits U N_old) (valBits V) w j := by
  set S_old := quotientBits U N_old + valBits V
  set S_new := quotientBits U N_new + valBits V
  have hwo_eq : wOffQ (quotientBits U N_old) (valBits V) w j = (j * S_old) / w := by
    have hid := wOffQ_mul_add_bOffQ
      (q_bits := quotientBits U N_old) (v_bits := valBits V) (w := w) (d := j)
    have hb := bOffQ_lt (q_bits := quotientBits U N_old) (v_bits := valBits V) (d := j) hw
    rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]
  rw [hwo_eq]
  have hj_iw : compactedItemWords U V w N_new j ≤ (j * S_new) / w + 3 := by
    change (j * S_new + w - 1) / w + 2 ≤ (j * S_new) / w + 3
    have := div_ceil_le_div_add_one (a := j * S_new) hw
    omega
  have hold_iw : compactedItemWords U V w N_old n ≤ (n * S_old) / w + 3 := by
    change (n * S_old + w - 1) / w + 2 ≤ (n * S_old) / w + 3
    have := div_ceil_le_div_add_one (a := n * S_old) hw
    omega
  have hnew_iw : (n * S_new) / w + 2 ≤ compactedItemWords U V w N_new n := by
    unfold compactedItemWords
    have : n * S_new ≤ n * S_new + w - 1 := by omega
    exact Nat.add_le_add_right (Nat.div_le_div_right this) 2
  unfold migrateArenaWords
  rcases le_total S_new S_old with hle | hge
  · have hmul : j * S_new ≤ j * S_old := Nat.mul_le_mul_left j hle
    have hdiv : (j * S_new) / w ≤ (j * S_old) / w := Nat.div_le_div_right hmul
    have hmax : compactedItemWords U V w N_old n ≤
        max (compactedItemWords U V w N_old n) (compactedItemWords U V w N_new n) :=
      le_max_left _ _
    omega
  · have hconv : j * S_new + n * S_old ≤ n * S_new + j * S_old := by
      have hsub : (n - j) * S_old ≤ (n - j) * S_new := Nat.mul_le_mul_left (n - j) hge
      have hnj : j + (n - j) = n := Nat.add_sub_of_le hj
      nlinarith
    have hdiv1 := div_add_div_le (a := j * S_new) (b := n * S_old) hw
    have hdiv2 : (j * S_new + n * S_old) / w ≤ (n * S_new + j * S_old) / w :=
      Nat.div_le_div_right hconv
    have hdiv3 := Nat.add_div_le_div_add_div_add_one (n * S_new) (j * S_old) w
    have hmax : compactedItemWords U V w N_new n ≤
        max (compactedItemWords U V w N_old n) (compactedItemWords U V w N_new n) :=
      le_max_right _ _
    have hmax_old : compactedItemWords U V w N_old n ≤
        max (compactedItemWords U V w N_old n) (compactedItemWords U V w N_new n) :=
      le_max_left _ _
    omega

theorem offCompItems_le_div_metaBits {U w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) (hN4 : N ≤ 4 * n) :
    offCompItems U w N ≤ (1344 * n * Dynamic.logLogFactor n + w - 1) / w + 439 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]; ring
  have hh := hashSpace_le hw hNU hU
  have h0 : packedWords (2 * N) 1 w = ((2 * N) * 1 + w - 1) / w + 2 := rfl
  have h1 := div_add_mul_packedWords_le 9 ((2 * N) * 1) 2 (totalMicroBuckets N)
    (effBucketPosBits N) w
  rw [hlm_eq] at h1
  have h2 := div_add_packedWords_le ((2 * N) * 1 + localMetaLen N * effBucketPosBits N) 29
    (globalMetaLen N) (globalPtrBits N) w
  have h3 := div_add_mul_packedWords_le 2
    ((2 * N) * 1 + localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N) 32
    (maxTailItems N) (globalPtrBits N) w
  have hmeta_le : offCompItems U w N ≤
      ((2 * N) * 1 + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N + w - 1) / w +
        439 := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
      epochHashSpace epochQBits epochHashB lmSubWords
    unfold hashSpace qBits hashB at hh
    omega
  have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
    (Dynamic.logLogFactor_mono hN4).trans (Dynamic.logLogFactor_four_mul_le n)
  have hll_N1 := Dynamic.one_le_logLogFactor N
  have hlm := localMetaLen_mul_effBucketPosBits_le N
  have hgm := globalMetaLen_mul_globalPtrBits_le N
  have htail := maxTailItems_mul_globalPtrBits_le N
  have h2tail : (2 * maxTailItems N) * globalPtrBits N ≤ 8 * N := by nlinarith
  have h10N : (2 * N) * 1 + (2 * maxTailItems N) * globalPtrBits N ≤
      10 * N * Dynamic.logLogFactor N := by
    have h10 : 10 * N ≤ 10 * N * Dynamic.logLogFactor N := by
      calc 10 * N = 10 * N * 1 := by ring
        _ ≤ 10 * N * Dynamic.logLogFactor N := by gcongr
    omega
  have h84N : (2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N ≤
      84 * N * Dynamic.logLogFactor N := by nlinarith
  have hN_ll : N * Dynamic.logLogFactor N ≤ 16 * (n * Dynamic.logLogFactor n) := by
    calc N * Dynamic.logLogFactor N
        ≤ (4 * n) * (4 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN4 hll_N
      _ = 16 * (n * Dynamic.logLogFactor n) := by ring
  have hnum0 : (2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N ≤
      1344 * n * Dynamic.logLogFactor n := by nlinarith
  have hnum : (2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N + w - 1 ≤
      1344 * n * Dynamic.logLogFactor n + w - 1 := by omega
  exact hmeta_le.trans (Nat.add_le_add_right (Nat.div_le_div_right hnum) 439)

private theorem compactedItemWords_le_div_optBits (U V w : ℕ) {N n : ℕ}
    (hnN : n ≤ N) (hN4 : N ≤ 4 * n) :
    compactedItemWords U V w N n ≤
      (Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n + w - 1) / w + 2 := by
  have hq6 := quotientBits_le_add_six_of_le_four_mul U hnN hN4
  have hqv_opt := quotient_val_bits_le_optBits (U := U) (V := V) (n := n)
  have hll_n := Dynamic.one_le_logLogFactor n
  have hmul : n * (quotientBits U N + valBits V) ≤
      n * (quotientBits U n + valBits V) + 6 * n := by
    calc n * (quotientBits U N + valBits V)
        ≤ n * (quotientBits U n + 6 + valBits V) := Nat.mul_le_mul_left n (by omega)
      _ = n * (quotientBits U n + valBits V) + 6 * n := by ring
  have h6n : 6 * n ≤ 6 * n * Dynamic.logLogFactor n := by
    calc 6 * n = 6 * n * 1 := by ring
      _ ≤ 6 * n * Dynamic.logLogFactor n := by gcongr
  have hnum0 : n * (quotientBits U N + valBits V) ≤
      Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by nlinarith
  have hnum : n * (quotientBits U N + valBits V) + w - 1 ≤
      Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n + w - 1 := by omega
  unfold compactedItemWords
  exact Nat.add_le_add_right (Nat.div_le_div_right hnum) 2

private theorem div_ceil_add_div_ceil_le {A B w : ℕ} (hw : 0 < w) :
    (A + w - 1) / w + (B + w - 1) / w ≤ (A + B + w - 1) / w + 1 := by
  have h1 := div_add_div_le (a := A + w - 1) (b := B + w - 1) hw
  have h2 : ((A + w - 1) + (B + w - 1)) / w ≤ (A + B + w - 1 + 1 * w) / w :=
    Nat.div_le_div_right (by omega)
  exact h1.trans (h2.trans_eq (Nat.add_mul_div_right (A + B + w - 1) 1 hw))

/-- **`1 · OPT` Migration Peak Word-Space Bound (`migratePeakWords_le_succinctWords`):**
Whenever `EpochValid U n N_old` and `1 ≤ n`, single-tape streaming capacity migration uses at most
`Dynamic.succinctWords 2699 888 U V w n` hardware words at peak — strictly `1 · OPT(U, V, n)` plus
lower-order `O(n log log n)` bits, never `2 · OPT`. -/
theorem migratePeakWords_le_succinctWords {U V w N_old n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hn : 1 ≤ n) (hev : EpochValid U n N_old) :
    migratePeakWords U V w N_old n ≤ Dynamic.succinctWords 2699 888 U V w n := by
  rcases hev with ⟨rfl, _⟩ | ⟨_, hn_old, hN4_old, hNU_old⟩
  · omega
  · have hnU : n ≤ U := hn_old.trans hNU_old
    have hev_new := epochValid_targetCap hnU
    rcases hev_new with ⟨rfl, _⟩ | ⟨_, hn_new, hN4_new, hNU_new⟩
    · omega
    · have hm_old := offCompItems_le_div_metaBits hw hNU_old hU.le hN4_old
      have hm_new := offCompItems_le_div_metaBits hw hNU_new hU.le hN4_new
      have hi_old := compactedItemWords_le_div_optBits U V w hn_old hN4_old
      have hi_new := compactedItemWords_le_div_optBits U V w hn_new hN4_new
      have har : migrateArenaWords U V w N_old (targetCap U n) n ≤
          (Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n + w - 1) / w + 8 := by
        unfold migrateArenaWords
        have hmax := max_le hi_old hi_new
        omega
      set M := 1344 * n * Dynamic.logLogFactor n
      set I := Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n
      have hc1 := div_ceil_add_div_ceil_le (A := M) (B := M) hw
      have hc2 := div_ceil_add_div_ceil_le (A := M + M) (B := I) hw
      have htot : M + M + I = Dynamic.optBits U V n + 2699 * n * Dynamic.logLogFactor n := by
        dsimp only [M, I]; ring
      rw [htot] at hc2
      unfold migratePeakWords Dynamic.succinctWords
      omega

/-- **`1 · OPT` Migration Peak Bit-Space Bound (`w_mul_migratePeakWords_le_bits`):**
Multiplying `migratePeakWords U V w N_old n` by `w` yields at most
`Dynamic.optBits U V n + 2699 * n * Dynamic.logLogFactor n + 889 * w` bits. -/
theorem w_mul_migratePeakWords_le_bits {U V w N_old n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hn : 1 ≤ n) (hev : EpochValid U n N_old) :
    w * migratePeakWords U V w N_old n ≤
      Dynamic.optBits U V n + 2699 * n * Dynamic.logLogFactor n + 889 * w := by
  calc w * migratePeakWords U V w N_old n
      ≤ w * Dynamic.succinctWords 2699 888 U V w n :=
        Nat.mul_le_mul_left w (migratePeakWords_le_succinctWords hw hU hn hev)
    _ ≤ Dynamic.optBits U V n + 2699 * n * Dynamic.logLogFactor n + (888 + 1) * w :=
        succinctWords_mul_w_le_bits 2699 888 U V w n

/-- Parameter-free `O(n)` word bound on `compactedItemWords`: every item uses `≤ 2 * w` bits, so
`compactedItemWords U V w N n ≤ 2 * n + 2` words for all `0 < w`, `U ≤ 2 ^ w`, `V ≤ 2 ^ w`. -/
theorem compactedItemWords_le_linear {U V w N n : ℕ}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) :
    compactedItemWords U V w N n ≤ 2 * n + 2 := by
  have hq : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  unfold compactedItemWords
  have hmul2 : n * (quotientBits U N + valBits V) ≤ (2 * n) * w := by
    calc n * (quotientBits U N + valBits V)
        ≤ n * (2 * w) := Nat.mul_le_mul_left n (by omega)
      _ = (2 * n) * w := by ring
  have hle : n * (quotientBits U N + valBits V) + w - 1 ≤ (w - 1) + (2 * n) * w := by omega
  calc (n * (quotientBits U N + valBits V) + w - 1) / w + 2
      ≤ ((w - 1) + (2 * n) * w) / w + 2 := Nat.add_le_add_right (Nat.div_le_div_right hle) 2
    _ = 2 * n + 2 := by
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]

private theorem logLogFactor_le_three_mul_w {w N : ℕ} (hw : 0 < w) (hN : Fits w N) :
    Dynamic.logLogFactor N ≤ 3 * w := by
  unfold Dynamic.logLogFactor
  have hmax : max N 4 ≤ 2 ^ (w + 2) := by
    have h4 : 4 ≤ 2 ^ (w + 2) := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right two_pos (by omega)
    have hNw : N ≤ 2 ^ (w + 2) :=
      hN.le.trans (Nat.pow_le_pow_right two_pos (by omega))
    exact max_le hNw h4
  have hc1 : Nat.clog 2 (max N 4) ≤ w + 2 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr hmax
  have hpow2 : w + 2 ≤ 2 ^ (3 * w) := by
    have hlt := @Nat.lt_two_pow_self (3 * w)
    omega
  exact (Nat.clog_mono_right 2 hc1).trans ((Nat.clog_le_iff_le_pow one_lt_two).mpr hpow2)

/-- Parameter-free `O(N)` word bound on `offCompItems U w N` (`≤ 252 * N + 439`) for all
`0 < w`, `N ≤ U`, and `Fits w U`, independent of `(U, V, w)`. -/
theorem offCompItems_le_linear {U w N : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) :
    offCompItems U w N ≤ 252 * N + 439 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]; ring
  have hh := hashSpace_le hw hNU hU.le
  have h0 : packedWords (2 * N) 1 w = ((2 * N) * 1 + w - 1) / w + 2 := rfl
  have h1 := div_add_mul_packedWords_le 9 ((2 * N) * 1) 2 (totalMicroBuckets N)
    (effBucketPosBits N) w
  rw [hlm_eq] at h1
  have h2 := div_add_packedWords_le ((2 * N) * 1 + localMetaLen N * effBucketPosBits N) 29
    (globalMetaLen N) (globalPtrBits N) w
  have h3 := div_add_mul_packedWords_le 2
    ((2 * N) * 1 + localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N) 32
    (maxTailItems N) (globalPtrBits N) w
  have hmeta_le : offCompItems U w N ≤
      ((2 * N) * 1 + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N + w - 1) / w +
        439 := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
      epochHashSpace epochQBits epochHashB lmSubWords
    unfold hashSpace qBits hashB at hh
    omega
  have hll_N1 := Dynamic.one_le_logLogFactor N
  have hlm := localMetaLen_mul_effBucketPosBits_le N
  have hgm := globalMetaLen_mul_globalPtrBits_le N
  have htail := maxTailItems_mul_globalPtrBits_le N
  have h84N : (2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N ≤
      84 * N * Dynamic.logLogFactor N := by
    have h10 : 10 * N ≤ 10 * N * Dynamic.logLogFactor N := by
      calc 10 * N = 10 * N * 1 := by ring
        _ ≤ 10 * N * Dynamic.logLogFactor N := by gcongr
    nlinarith
  have hll_w : Dynamic.logLogFactor N ≤ 3 * w := logLogFactor_le_three_mul_w hw (hU.of_le hNU)
  have h252_0 : 84 * N * Dynamic.logLogFactor N ≤ (252 * N) * w := by
    calc 84 * N * Dynamic.logLogFactor N
        ≤ 84 * N * (3 * w) := Nat.mul_le_mul_left (84 * N) hll_w
      _ = (252 * N) * w := by ring
  have h252 : 84 * N * Dynamic.logLogFactor N + w - 1 ≤ (w - 1) + (252 * N) * w := by omega
  have hdiv : ((2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N + w - 1) / w ≤
      252 * N := by
    calc _ ≤ ((w - 1) + (252 * N) * w) / w := Nat.div_le_div_right (by omega)
      _ = 252 * N := by
          rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]
  omega

/-- Parameter-free `O(n)` linear word bound on `migratePeakWords` (`≤ 1514 * n + 886`), ensuring
that word-zeroing, word-shifting, `growZeroCode`, and `shrinkCode` all run in `O(n)` instructions
with constants completely independent of `(U, V, w)`. -/
theorem migratePeakWords_le_linear {U V w N_old n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w) (hn : 1 ≤ n) (hev : EpochValid U n N_old) :
    migratePeakWords U V w N_old n ≤ 1514 * n + 886 := by
  rcases hev with ⟨rfl, _⟩ | ⟨_, hn_old, hN4_old, hNU_old⟩
  · omega
  · have hnU : n ≤ U := hn_old.trans hNU_old
    have htc_le_U : targetCap U n ≤ U := by
      unfold targetCap; rw [ite_eq_right (by omega)]; exact min_le_right _ _
    have htc_le_2n : targetCap U n ≤ 2 * n := by
      unfold targetCap; rw [ite_eq_right (by omega)]; exact min_le_left _ _
    have hm_old := (offCompItems_le_linear hw hNU_old hU).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 252 hN4_old) 439)
    have hm_new := (offCompItems_le_linear hw htc_le_U hU).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 252 htc_le_2n) 439)
    have hi_old := compactedItemWords_le_linear (N := N_old) (n := n) hw hU.le hV
    have hi_new := compactedItemWords_le_linear (N := targetCap U n) (n := n) hw hU.le hV
    unfold migratePeakWords migrateArenaWords
    have hmax := max_le hi_old hi_new
    omega

/-! ## Section 2: Overflow-Free `packedWords` and Bounded `log2` / `trinomial` / `pow3` Loops -/

/-- Overflow-free identity `packedWords len k w = wordOffset k w len + (2 or 3)` for `0 < w`. -/
private theorem packedWords_eq_wordOffset_add {len k w : ℕ} (hw : 0 < w) :
    packedWords len k w =
      wordOffset k w len + (if bitOffset k w len = 0 then 2 else 3) := by
  unfold packedWords
  have hid := wordOffset_mul_add_bitOffset (k := k) (w := w) (idx := len)
  have hb_lt : bitOffset k w len < w := bitOffset_lt hw
  rw [← hid]
  set W := wordOffset k w len
  set B := bitOffset k w len
  split_ifs with hB0
  · have heq : W * w + B + w - 1 = (w - 1) + W * w := by omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : w - 1 < w), Nat.zero_add]
  · have heq : W * w + B + w - 1 = (B - 1) + (W + 1) * w := by
      rw [Nat.add_one_mul]; omega
    rw [heq, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega : B - 1 < w), Nat.zero_add]

/-- Overflow-free evaluator for `packedWords len k w` in `Memory.Prog` (`¬ReadsWidth`). -/
private def compPackedWordsProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((len, k), wVal) => do
    let prodMod := (len % wVal) * k
    let wOff := (len / wVal) * k + prodMod / wVal
    let bOff := prodMod % wVal
    let z0 ← pure 0
    if bOff = z0 then pure (wOff + 2) else pure (wOff + 3)

@[simp] private theorem clientResult_compPackedWordsProg {len k w : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (compPackedWordsProg ((len, k), w)) = packedWords len k w := by
  rw [packedWords_eq_wordOffset_add hw]
  unfold compPackedWordsProg wordOffset bitOffset
  simp only [pure_bind, Nat.mod_mul_mod]
  split_ifs <;> simp only [prog_clientResult_pure]

private theorem clientState_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (compPackedWordsProg d) = s := by
  rcases d with ⟨⟨len, k⟩, wVal⟩
  dsimp only [compPackedWordsProg]
  simp only [pure_bind]
  split_ifs <;> rfl

@[simp] private theorem runClient_state_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (compPackedWordsProg d))) = s :=
  clientState_compPackedWordsProg d s

@[simp] private theorem memoryCost_compPackedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (compPackedWordsProg d) s = 0 := by
  rcases d with ⟨⟨len, k⟩, wVal⟩
  dsimp only [compPackedWordsProg]
  simp only [pure_bind]
  split_ifs <;> rfl

private def CompPackedWordsPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((len, k), wVal), _s =>
    0 < w ∧ wVal = w ∧ k ≤ w ∧ Fits w len ∧ Fits w (packedWords len k w) ∧ Fits w 3

private theorem realizesBounded_compPackedWords :
    RealizesBounded .exact compPackedWordsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompPackedWordsPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨len, k⟩, wVal⟩
    obtain ⟨hw, hwVal, hkw, hlen, hpw, hfit3⟩ := h
    subst wVal
    dsimp only at *
    rw [packedWords_eq_wordOffset_add hw] at hpw
    unfold wordOffset bitOffset at hpw
    simp only [Nat.mod_mul_mod] at *)
  all_goals try exact hw.ne'
  all_goals try exact mod_mul_lt_two_pow hw hkw len
  all_goals (
    split_ifs at hpw
    exact hpw.of_le (by omega))

/-- Evaluate `targetCap U n = if n = 0 then 0 else min (2 * n) U` from `[hdrBase]` (`= U - 1`)
without intermediate `2 * n` overflow (`¬ReadsWidth`). -/
def computeTargetCapProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrBase, n) => do
    let z0 ← pure 0
    if n = z0 then pure 0
    else do
      let uSub1 ← Memory.read hdrBase
      let uVal ← pure (uSub1 + 1)
      let rem ← pure (uVal - n)
      if rem < n then pure uVal else pure (n + n)

/-- Precondition for `computeTargetCapProg`. -/
@[expose] def ComputeTargetCapPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrBase, n), s =>
    hdrBase < s.frontier ∧ Fits w (s.mem hdrBase + 1) ∧ n ≤ s.mem hdrBase + 1 ∧ Fits w 1

theorem realizesBounded_computeTargetCap :
    RealizesBounded .exact computeTargetCapProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      ComputeTargetCapPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrBase, n⟩
    obtain ⟨hfr, hU, hnU, h1⟩ := h
    dsimp only at *)
  all_goals try omega
  exact hU.of_le (by omega)

theorem computeTargetCapProg_spec {w U V N_old n_hdr n_init_hdr hdrBase n : ℕ} {s : Memory.State}
    (hhdr : RootHeaderValid U V w N_old n_hdr n_init_hdr hdrBase s.mem)
    (hfr : hdrBase < s.frontier) (hnU : n ≤ U) (hfit1 : Fits w 1) :
    ComputeTargetCapPre w (hdrBase, n) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (computeTargetCapProg (hdrBase, n))) ∧
    (Memory.spec 0).clientState s (computeTargetCapProg (hdrBase, n)) = s ∧
    (Memory.spec 0).clientResult s (computeTargetCapProg (hdrBase, n)) = targetCap U n ∧
    memoryCost (computeTargetCapProg (hdrBase, n)) s ≤ 1 := by
  have hu_eq : s.mem hdrBase + 1 = U := by have := hhdr.pos_U; rw [hhdr.hdr_U]; omega
  have hpre : ComputeTargetCapPre w (hdrBase, n) s :=
    ⟨hfr, hu_eq.symm ▸ hhdr.fits_U, hu_eq.symm ▸ hnU, hfit1⟩
  refine ⟨hpre, ?_, ?_, ?_, ?_⟩
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · trivial
    · rw [validHistory_bind']; refine ⟨⟨hfr, trivial⟩, ?_⟩
      simp only [prog_clientResult_read, StateTransitionSpec.clientState, prog_runClient_state_read]
      by_cases hlt : s.mem hdrBase + 1 - n < n <;> simp only [hlt, ↓reduceIte] <;> trivial
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · rfl
    · rw [StateTransitionSpec.clientState_bind, prog_clientResult_read]
      have hs0 : (Memory.spec 0).clientState s (Memory.read hdrBase) = s := rfl
      rw [hs0]
      split_ifs <;> rfl
  · dsimp only [computeTargetCapProg, targetCap]; simp only [pure_bind]
    split_ifs with hn0
    · rfl
    · simp only [prog_clientResult_bind, prog_clientResult_read, StateTransitionSpec.clientState,
        prog_runClient_state_read, hu_eq]
      split_ifs with hlt <;> simp only [prog_clientResult_pure]
      · exact (Nat.min_eq_right (by omega)).symm
      · rw [Nat.min_eq_left (by omega)]; omega
  · dsimp only [computeTargetCapProg]; simp only [pure_bind]
    split_ifs with hn0
    · exact Nat.zero_le 1
    · simp only [Realization.memoryCost_bind', prog_memoryCost_read,
        StateTransitionSpec.clientState, prog_runClient_state_read]
      split_ifs <;> exact le_rfl

/-- Pure recurrence matching `K` steps of capped floor-`log₂`:
`log2CapStep (rem, acc) = if 1 < rem then (rem / 2, acc + 1) else (rem, acc)`. -/
private def log2CapAux : ℕ → ℕ → ℕ × ℕ
  | 0, rem => (rem, 0)
  | k + 1, rem =>
    if 1 < rem then
      let p := log2CapAux k (rem / 2)
      (p.1, p.2 + 1)
    else (rem, 0)

private theorem log2CapAux_snd (k rem : ℕ) : (log2CapAux k rem).2 = min k (Nat.log 2 rem) := by
  induction k generalizing rem with
  | zero => simp [log2CapAux]
  | succ k ih =>
    dsimp only [log2CapAux]
    split_ifs with h1
    · have hlog : Nat.log 2 rem = Nat.log 2 (rem / 2) + 1 :=
        Nat.log_of_one_lt_of_le one_lt_two h1
      rw [ih (rem / 2), hlog]
      omega
    · have hlog0 : Nat.log 2 rem = 0 := Nat.log_of_lt (by omega)
      simp [hlog0]

private theorem log2CapAux_step (k rem acc : ℕ) :
    let next := if 1 < rem then (rem / 2, acc + 1) else (rem, acc)
    next.2 + (log2CapAux k next.1).2 = acc + (log2CapAux (k + 1) rem).2 := by
  dsimp only [log2CapAux]
  split_ifs with h1
  · dsimp only; omega
  · have h0 : (log2CapAux k rem).2 = 0 := by
      rw [log2CapAux_snd, Nat.log_of_lt (by omega), Nat.min_zero]
    dsimp only; omega

private def log2StepProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (hdrAddr, (rem, acc)) => do
    let _ ← Memory.read hdrAddr
    if 1 < rem then pure (rem >>> 1, acc + 1) else pure (rem, acc)

private theorem clientState_log2StepProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (log2StepProg x) = s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  rw [StateTransitionSpec.clientState_bind]
  have hs0 : (Memory.spec 0).clientState s (Memory.read hdrAddr) = s := rfl
  rw [hs0]
  split_ifs <;> rfl

private theorem validHistory_log2StepProg {w hdrAddr rem acc : ℕ} {s : Memory.State}
    (hfr : hdrAddr < s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (log2StepProg (hdrAddr, (rem, acc)))) := by
  dsimp only [log2StepProg]
  rw [validHistory_bind']; refine ⟨⟨hfr, trivial⟩, ?_⟩
  simp only [StateTransitionSpec.clientState, prog_runClient_state_read]
  split_ifs <;> trivial

private def Log2StepPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (rem, acc)), s =>
    hdrAddr < s.frontier ∧ Fits w rem ∧ Fits w (acc + 1)

private theorem realizesBounded_log2Step :
    RealizesBounded .exact log2StepProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      Log2StepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrAddr, ⟨rem, acc⟩⟩
    obtain ⟨hfr, hrem, hacc1⟩ := h
    try dsimp only at *)
  all_goals try omega
  all_goals exact hacc1.of_le (by omega)

private theorem memoryCost_log2Step_ge_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (log2StepProg x) s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]
  split_ifs <;> omega

private theorem memoryCost_log2Step_le_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (log2StepProg x) s ≤ 1 := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [log2StepProg]
  simp only [Realization.memoryCost_bind', prog_memoryCost_read, StateTransitionSpec.clientState,
    prog_runClient_state_read]
  split_ifs <;> exact le_rfl

private theorem log2Loop_spec {w hdrAddr K x₀ : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hx₀ : Fits w x₀) (hK : Fits w (min K (Nat.log 2 x₀) + 1)) :
    let prog := iterate log2StepProg hdrAddr K (x₀, 0)
    iterationSafe log2StepProg Log2StepPre w hdrAddr K (x₀, 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ K ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2 = min K (Nat.log 2 x₀) := by
  intro prog
  let inv (k : ℕ) (st : ℕ × ℕ) (s : Memory.State) : Prop :=
    s = s₀ ∧ st.1 ≤ x₀ ∧ st.2 + (log2CapAux (K - k) st.1).2 = (log2CapAux K x₀).2 ∧
    st.2 ≤ min K (Nat.log 2 x₀)
  obtain ⟨hsafe, hv, hcost, _, _, hs_eq, _, hsum_end, _⟩ :=
    iterate_spec log2StepProg Log2StepPre w hdrAddr 1 K inv (fun _ => False)
      (fun k hk st s ⟨hs_eq, hle_x, hsum, hacc_le⟩ => by
        subst hs_eq
        rcases st with ⟨rem, acc⟩
        change rem ≤ x₀ at hle_x
        change acc + (log2CapAux (K - k) rem).2 = (log2CapAux K x₀).2 at hsum
        change acc ≤ min K (Nat.log 2 x₀) at hacc_le
        have hrem_fit : Fits w rem := hx₀.of_le hle_x
        have hacc1_fit : Fits w (acc + 1) := hK.of_le (by omega)
        have hs' := clientState_log2StepProg (hdrAddr, (rem, acc)) s
        refine ⟨⟨hfr, hrem_fit, hacc1_fit⟩, validHistory_log2StepProg hfr,
          memoryCost_log2Step_le_one _ _,
          congrArg Memory.State.frontier hs',
          (fun _ _ => by rw [hs']),
          hs', ?_, ?_, ?_⟩
        · dsimp only [log2StepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs
          · rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_le_self _ _).trans hle_x
          · exact hle_x
        · dsimp only [log2StepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          have hsub : K - k = (K - (k + 1)) + 1 := by omega
          have hst := log2CapAux_step (K - (k + 1)) rem acc
          dsimp only at hst
          rw [← hsub] at hst
          split_ifs with h1 <;>
            simp only [h1, ↓reduceIte, prog_clientResult_pure, Nat.shiftRight_eq_div_pow,
              pow_one] at hst ⊢
          · exact hst.trans hsum
          · exact hst.trans hsum
        · dsimp only [log2StepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs with h1
          · dsimp only [prog_clientResult_pure]
            have hpos : 1 ≤ (log2CapAux (K - k) rem).2 := by
              rw [log2CapAux_snd]
              exact le_min (by omega) (Nat.le_log_of_pow_le one_lt_two (by omega))
            rw [log2CapAux_snd K x₀] at hsum
            omega
          · exact hacc_le)
      (x₀, 0) s₀ ⟨rfl, le_rfl, by simp, Nat.zero_le _⟩
  refine ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs_eq, ?_⟩
  rw [Nat.sub_self] at hsum_end
  dsimp only [log2CapAux] at hsum_end
  rw [Nat.add_zero] at hsum_end
  exact hsum_end.trans (log2CapAux_snd K x₀)

private def log2CapProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (hdrAddr, (K, x₀)) => do
    let (_, res) ← iterate log2StepProg hdrAddr K (x₀, 0)
    pure res

private def Log2CapPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (K, x₀)), s =>
    hdrAddr < s.frontier ∧ Fits w x₀ ∧ Fits w (min K (Nat.log 2 x₀) + 1)

private theorem realizesBounded_log2Cap :
    RealizesBounded .exact log2CapProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      Log2CapPre (fun _ _ => 0) := by
  have hlg := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ × ℕ)) realizesBounded_log2Step memoryCost_log2Step_ge_one
  realize
  rcases d with ⟨hdrAddr, ⟨K, x₀⟩⟩
  obtain ⟨hfr, hx₀, hK⟩ := h
  exact (log2Loop_spec hfr hx₀ hK).1

private theorem log2CapProg_spec {w hdrAddr K x₀ : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hx₀ : Fits w x₀) (hK : Fits w (min K (Nat.log 2 x₀) + 1)) :
    let prog := log2CapProg (hdrAddr, (K, x₀))
    Log2CapPre w (hdrAddr, (K, x₀)) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ K ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = min K (Nat.log 2 x₀) := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := log2Loop_spec hfr hx₀ hK
  refine ⟨⟨hfr, hx₀, hK⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, log2CapProg]
    rw [validHistory_bind', hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate log2StepProg hdrAddr K (x₀, 0)) with ⟨_, _⟩
    exact ⟨hv, trivial⟩
  · dsimp only [prog, log2CapProg]
    rw [Realization.memoryCost_bind', hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate log2StepProg hdrAddr K (x₀, 0)) with ⟨_, _⟩
    dsimp only; rw [memoryCost_pure]; omega
  · dsimp only [prog, log2CapProg]
    rw [StateTransitionSpec.clientState_bind, hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate log2StepProg hdrAddr K (x₀, 0)) with ⟨_, _⟩
    rfl
  · dsimp only [prog, log2CapProg]
    rw [prog_clientResult_bind, hst]
    rcases hp : (Memory.spec 0).clientResult s₀ (iterate log2StepProg hdrAddr K (x₀, 0)) with ⟨_, r⟩
    dsimp only; rw [prog_clientResult_pure, ← hres, hp]

/-- Exact ceiling-to-floor binary logarithm identity `⌈log₂ x⌉ = ⌊log₂ (x - 1)⌋ + 1` for `1 < x`. -/
private theorem clog2_eq_log2_pred_add_one {x : ℕ} (hx : 1 < x) :
    Nat.clog 2 x = Nat.log 2 (x - 1) + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow one_lt_two]
    have hlt := Nat.lt_pow_succ_log_self one_lt_two (x - 1)
    omega
  · have hpos : 0 < Nat.clog 2 x := Nat.clog_pos one_lt_two hx
    have hle_c : x - 1 < 2 ^ Nat.clog 2 x := by
      have := Nat.le_pow_clog one_lt_two x; omega
    have hlt_log : Nat.log 2 (x - 1) < Nat.clog 2 x :=
      (Nat.log_lt_iff_lt_pow one_lt_two (by omega)).mpr hle_c
    omega

private theorem clog2_succ_eq_log2_add_one {m : ℕ} (hm : 1 ≤ m) :
    Nat.clog 2 (m + 1) = Nat.log 2 m + 1 := by
  rw [clog2_eq_log2_pred_add_one (by omega), Nat.add_sub_cancel]

/-- Bounded step for `trinomialStepAux B`:
`if 2 < rem then ((rem + 2) / 3, acc + 1) else (rem, acc)`. -/
private def trinomStepProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (hdrAddr, (rem, acc)) => do
    let _ ← Memory.read hdrAddr
    if 2 < rem then pure ((rem + 2) / 3, acc + 1) else pure (rem, acc)

private theorem clientState_trinomStepProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (trinomStepProg x) = s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [trinomStepProg]
  rw [StateTransitionSpec.clientState_bind]
  have hs0 : (Memory.spec 0).clientState s (Memory.read hdrAddr) = s := rfl
  rw [hs0]
  split_ifs <;> rfl

private theorem validHistory_trinomStepProg {w hdrAddr rem acc : ℕ} {s : Memory.State}
    (hfr : hdrAddr < s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (trinomStepProg (hdrAddr, (rem, acc)))) := by
  dsimp only [trinomStepProg]
  rw [validHistory_bind']; refine ⟨⟨hfr, trivial⟩, ?_⟩
  simp only [StateTransitionSpec.clientState, prog_runClient_state_read]
  split_ifs <;> trivial

private def TrinomStepPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (rem, acc)), s =>
    hdrAddr < s.frontier ∧ Fits w (rem + 2) ∧ Fits w (acc + 1) ∧ Fits w 3

private theorem realizesBounded_trinomStep :
    RealizesBounded .exact trinomStepProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      TrinomStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrAddr, ⟨rem, acc⟩⟩
    obtain ⟨hfr, hrem2, hacc1, h3⟩ := h
    try dsimp only at *)
  all_goals try omega
  exact h3.of_le (by omega)

private theorem memoryCost_trinomStep_ge_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (trinomStepProg x) s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [trinomStepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]
  split_ifs <;> omega

private theorem memoryCost_trinomStep_le_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (trinomStepProg x) s ≤ 1 := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [trinomStepProg]
  simp only [Realization.memoryCost_bind', prog_memoryCost_read, StateTransitionSpec.clientState,
    prog_runClient_state_read]
  split_ifs <;> exact le_rfl

private theorem trinomLoop_spec {w hdrAddr B : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hB2 : Fits w (B + 2)) (h3 : Fits w 3) :
    let prog := iterate trinomStepProg hdrAddr B (B, 0)
    iterationSafe trinomStepProg TrinomStepPre w hdrAddr B (B, 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ B ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2 = trinomialStepAux B := by
  intro prog
  have ht_le : trinomialStepAux B ≤ B :=
    Cslib.DataStructure.HashFamily.WordRAM.KWise.trinomialStepAux_le B
  let inv (k : ℕ) (st : ℕ × ℕ) (s : Memory.State) : Prop :=
    s = s₀ ∧ st.1 ≤ B ∧ st.1 ≤ B - k + 2 ∧
    st.2 + trinomialStepAux st.1 = trinomialStepAux B
  obtain ⟨hsafe, hv, hcost, _, _, hs_eq, _, hrem_end, hsum_end⟩ :=
    iterate_spec trinomStepProg TrinomStepPre w hdrAddr 1 B inv (fun _ => False)
      (fun k hk st s ⟨hs_eq, hle_B, hrem_bd, hsum⟩ => by
        subst hs_eq
        rcases st with ⟨rem, acc⟩
        dsimp only at hle_B hrem_bd hsum
        have hacc_le : acc ≤ trinomialStepAux B := by omega
        have hs' := clientState_trinomStepProg (hdrAddr, (rem, acc)) s
        refine ⟨⟨hfr, hB2.of_le (by omega), hB2.of_le (by omega), h3⟩,
          validHistory_trinomStepProg hfr,
          memoryCost_trinomStep_le_one _ _,
          congrArg Memory.State.frontier hs',
          (fun _ _ => by rw [hs']),
          hs', ?_, ?_, ?_⟩
        · dsimp only [trinomStepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs with h2
          · exact (show (rem + 2) / 3 ≤ rem by omega).trans hle_B
          · exact hle_B
        · dsimp only [trinomStepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs with h2 <;> simp only [prog_clientResult_pure] <;> omega
        · dsimp only [trinomStepProg]
          simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
            prog_runClient_state_read]
          split_ifs with h2
          · dsimp only [prog_clientResult_pure]
            have hrec : trinomialStepAux rem = trinomialStepAux ((rem + 2) / 3) + 1 := by
              rw [trinomialStepAux, ite_eq_right (by omega)]
            omega
          · exact hsum)
      (B, 0) s₀ ⟨rfl, le_rfl, by omega, Nat.zero_add _⟩
  refine ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs_eq, ?_⟩
  dsimp only [prog] at *
  have h0 : trinomialStepAux
      ((Memory.spec 0).clientResult s₀ (iterate trinomStepProg hdrAddr B (B, 0))).1 = 0 := by
    rw [trinomialStepAux, ite_eq_left (by omega)]
  omega

private def trinomProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, B) => do
    let (_, res) ← iterate trinomStepProg hdrAddr B (B, 0)
    pure res

private def TrinomPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, B), s => hdrAddr < s.frontier ∧ Fits w (B + 2) ∧ Fits w 3

private theorem realizesBounded_trinom :
    RealizesBounded .exact trinomProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      TrinomPre (fun _ _ => 0) := by
  have htr := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ × ℕ)) realizesBounded_trinomStep memoryCost_trinomStep_ge_one
  realize
  rcases d with ⟨hdrAddr, B⟩
  obtain ⟨hfr, hB2, h3⟩ := h
  exact (trinomLoop_spec hfr hB2 h3).1

private theorem trinomProg_spec {w hdrAddr B : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hB2 : Fits w (B + 2)) (h3 : Fits w 3) :
    let prog := trinomProg (hdrAddr, B)
    TrinomPre w (hdrAddr, B) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ B ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = trinomialStepAux B := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := trinomLoop_spec hfr hB2 h3
  refine ⟨⟨hfr, hB2, h3⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, trinomProg]
    rw [validHistory_bind', hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate trinomStepProg hdrAddr B (B, 0)) with ⟨_, _⟩
    exact ⟨hv, trivial⟩
  · dsimp only [prog, trinomProg]
    rw [Realization.memoryCost_bind', hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate trinomStepProg hdrAddr B (B, 0)) with ⟨_, _⟩
    dsimp only; rw [memoryCost_pure]; omega
  · dsimp only [prog, trinomProg]
    rw [StateTransitionSpec.clientState_bind, hst]
    rcases (Memory.spec 0).clientResult s₀ (iterate trinomStepProg hdrAddr B (B, 0)) with ⟨_, _⟩
    rfl
  · dsimp only [prog, trinomProg]
    rw [prog_clientResult_bind, hst]
    rcases hp : (Memory.spec 0).clientResult s₀
      (iterate trinomStepProg hdrAddr B (B, 0)) with ⟨_, r⟩
    dsimp only; rw [prog_clientResult_pure, ← hres, hp]

/-- Bounded step computing `3 ^ e`: `acc ↦ 3 * acc`. -/
private def pow3StepProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, acc) => do
    let _ ← Memory.read hdrAddr
    pure (acc + acc + acc)

private def Pow3StepPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, acc), s => hdrAddr < s.frontier ∧ Fits w (3 * acc)

private theorem realizesBounded_pow3Step :
    RealizesBounded .exact pow3StepProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      Pow3StepPre (fun _ _ => 0) := by
  realize
  rcases d with ⟨hdrAddr, acc⟩
  obtain ⟨hfr, h3⟩ := h
  dsimp only at *
  exact h3.of_le (by omega)

private theorem memoryCost_pow3Step_ge_one (x : ℕ × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pow3StepProg x) s := by
  rcases x with ⟨hdrAddr, acc⟩
  dsimp only [pow3StepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]; omega

private theorem pow3Loop_spec {w hdrAddr e : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hfit : Fits w (3 ^ e)) :
    let prog := iterate pow3StepProg hdrAddr e 1
    iterationSafe pow3StepProg Pow3StepPre w hdrAddr e 1 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ e ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = 3 ^ e := by
  intro prog
  let inv (k : ℕ) (acc : ℕ) (s : Memory.State) : Prop := s = s₀ ∧ acc = 3 ^ k
  obtain ⟨hsafe, hv, hcost, _, _, hs_eq, hres_eq⟩ :=
    iterate_spec pow3StepProg Pow3StepPre w hdrAddr 1 e inv (fun _ => False)
      (fun k hk acc s ⟨hs_eq, hacc⟩ => by
        subst hs_eq; subst hacc
        have hle : 3 * 3 ^ k ≤ 3 ^ e := by
          calc 3 * 3 ^ k = 3 ^ (k + 1) := by rw [pow_succ']
            _ ≤ 3 ^ e := Nat.pow_le_pow_right (by decide) hk
        refine ⟨⟨hfr, hfit.of_le hle⟩, ⟨hfr, trivial⟩, le_rfl, rfl, (fun _ _ => rfl),
          rfl, ?_⟩
        dsimp only [pow3StepProg]
        simp only [prog_clientResult_bind, prog_clientResult_pure]
        rw [pow_succ]; ring)
      1 s₀ ⟨rfl, rfl⟩
  exact ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs_eq, hres_eq⟩

private def pow3Prog : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, e) => do
    let res ← iterate pow3StepProg hdrAddr e 1
    let z ← pure 0
    pure (res + z)

private def Pow3Pre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, e), s => hdrAddr < s.frontier ∧ Fits w (3 ^ e)

private theorem realizesBounded_pow3 :
    RealizesBounded .exact pow3Prog
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      Pow3Pre (fun _ _ => 0) := by
  have hp3 := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ)) realizesBounded_pow3Step memoryCost_pow3Step_ge_one
  realize
  all_goals (
    rcases d with ⟨hdrAddr, e⟩
    obtain ⟨hfr, hfit⟩ := h
    dsimp only at *
    first
    | exact (pow3Loop_spec hfr hfit).1
    | exact hfit.of_le (Nat.one_le_pow e 3 (by decide))
    | (rw [(pow3Loop_spec hfr hfit).2.2.2.2]; exact hfit))

private theorem pow3Prog_spec {w hdrAddr e : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hfit : Fits w (3 ^ e)) :
    let prog := pow3Prog (hdrAddr, e)
    Pow3Pre w (hdrAddr, e) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ e ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = 3 ^ e := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := pow3Loop_spec hfr hfit
  refine ⟨⟨hfr, hfit⟩, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, pow3Prog]; simp only [pure_bind, Nat.add_zero]
    rw [validHistory_bind', hst]
    exact ⟨hv, trivial⟩
  · dsimp only [prog, pow3Prog]; simp only [pure_bind, Nat.add_zero]
    rw [Realization.memoryCost_bind', hst, memoryCost_pure]; omega
  · dsimp only [prog, pow3Prog]; simp only [pure_bind, Nat.add_zero]
    rw [StateTransitionSpec.clientState_bind, hst, StateTransitionSpec.clientState_pure]
  · dsimp only [prog, pow3Prog]; simp only [pure_bind, Nat.add_zero]
    rw [prog_clientResult_bind, hst, prog_clientResult_pure, hres]

/-! ## Section 3: Runtime `HashParams` and `CompParams` Writer (`writeEpochParamsGenProg`) -/

private theorem validHistory_read_step {α : Type} {w a fr : ℕ} {mem : ℕ → ℕ}
    {k : ℕ → Memory.Prog α} (ha : a < fr)
    (hk : (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (k (mem a)))) :
    (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (Memory.read a >>= k)) :=
  ⟨ha, hk⟩

private theorem validHistory_write_step {α : Type} {w a v fr : ℕ} {mem : ℕ → ℕ}
    {k : Unit → Memory.Prog α} (ha : a < fr) (hv : Fits w v)
    (hk : (Memory.spec w).ValidHistory { mem := Function.update mem a v, frontier := fr }
      ((Memory.spec w).clientHistory { mem := Function.update mem a v, frontier := fr }
        (k ()))) :
    (Memory.spec w).ValidHistory { mem := mem, frontier := fr }
      ((Memory.spec w).clientHistory { mem := mem, frontier := fr } (Memory.write a v >>= k)) :=
  ⟨⟨ha, hv⟩, hk⟩

private def subSatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure 0 else pure (a - b)

@[simp] private theorem clientResult_subSatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (subSatProg (a, b)) = a - b := by
  dsimp only [subSatProg]
  split_ifs with h
  · simp only [prog_clientResult_pure]; omega
  · simp only [prog_clientResult_pure]

private theorem clientState_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (subSatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (subSatProg p))) = s :=
  clientState_subSatProg p s

@[simp] private theorem memoryCost_subSatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (subSatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> rfl

private theorem validHistory_subSatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subSatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [subSatProg]; split_ifs <;> trivial

private theorem realizesBounded_subSat :
    RealizesBounded .exact subSatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  rcases d with ⟨a, b⟩
  dsimp only at *
  omega

private def minNatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure a else pure b

@[simp] private theorem clientResult_minNatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (minNatProg (a, b)) = min a b := by
  dsimp only [minNatProg]
  split_ifs with h <;> simp only [prog_clientResult_pure]
  · exact (Nat.min_eq_left h.le).symm
  · exact (Nat.min_eq_right (Nat.le_of_not_lt h)).symm

private theorem clientState_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (minNatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (minNatProg p))) = s :=
  clientState_minNatProg p s

@[simp] private theorem memoryCost_minNatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minNatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> rfl

private theorem validHistory_minNatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minNatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [minNatProg]; split_ifs <;> trivial

private theorem realizesBounded_minNat :
    RealizesBounded .exact minNatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def maxNatProg : ℕ × ℕ → Memory.Prog ℕ
  | (a, b) => if a < b then pure b else pure a

@[simp] private theorem clientResult_maxNatProg (a b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (maxNatProg (a, b)) = max a b := by
  dsimp only [maxNatProg]
  split_ifs with h <;> simp only [prog_clientResult_pure]
  · exact (Nat.max_eq_right h.le).symm
  · exact (Nat.max_eq_left (Nat.le_of_not_lt h)).symm

private theorem clientState_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (maxNatProg p) = s := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (maxNatProg p))) = s :=
  clientState_maxNatProg p s

@[simp] private theorem memoryCost_maxNatProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (maxNatProg p) s = 0 := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> rfl

private theorem validHistory_maxNatProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (maxNatProg p)) := by
  rcases p with ⟨a, b⟩; dsimp only [maxNatProg]; split_ifs <;> trivial

private theorem realizesBounded_maxNat :
    RealizesBounded .exact maxNatProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def ifEqZeroProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (x, (tVal, fVal)) => do
    let z0 ← pure 0
    if x = z0 then pure tVal else pure fVal

@[simp] private theorem clientResult_ifEqZeroProg (x tVal fVal : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (ifEqZeroProg (x, (tVal, fVal))) =
      if x = 0 then tVal else fVal := by
  dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> simp only [prog_clientResult_pure]

private theorem clientState_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (ifEqZeroProg p) = s := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> rfl

@[simp] private theorem runClient_state_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (ifEqZeroProg p))) = s :=
  clientState_ifEqZeroProg p s

@[simp] private theorem memoryCost_ifEqZeroProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (ifEqZeroProg p) s = 0 := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> rfl

private theorem validHistory_ifEqZeroProg {w : ℕ} (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ifEqZeroProg p)) := by
  rcases p with ⟨x, ⟨tVal, fVal⟩⟩; dsimp only [ifEqZeroProg]; simp only [pure_bind]
  split_ifs <;> trivial

private theorem realizesBounded_ifEqZero :
    RealizesBounded .exact ifEqZeroProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

private def minEffCapProg : ℕ × ℕ → Memory.Prog ℕ
  | (N, numMicro) => if (N >>> 2) < numMicro then pure N else pure (numMicro <<< 2)

@[simp] private theorem clientResult_minEffCapProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (minEffCapProg (N, numMicroPerBucket N)) =
      min N (effBucketCap N) := by
  dsimp only [minEffCapProg]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (Memory.spec 0).clientResult s
    (if N / 4 < numMicroPerBucket N then pure N else pure (numMicroPerBucket N * 4)) =
    min N (4 * numMicroPerBucket N)
  rw [Nat.mul_comm (numMicroPerBucket N) 4]
  split_ifs with hlt <;> simp only [prog_clientResult_pure]
  · exact (Nat.min_eq_left (by omega)).symm
  · exact (Nat.min_eq_right (by omega)).symm

private theorem clientState_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (minEffCapProg p) = s := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (minEffCapProg p))) = s :=
  clientState_minEffCapProg p s

@[simp] private theorem memoryCost_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minEffCapProg p) s = 0 := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> rfl

private theorem validHistory_minEffCapProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minEffCapProg p)) := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> trivial

private def MinEffCapPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (N, _), _ => Fits w 2 ∧ Fits w N

private theorem realizesBounded_minEffCap :
    RealizesBounded .exact minEffCapProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      MinEffCapPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨N, numMicro⟩
    obtain ⟨h2, hN_fit⟩ := h
    try dsimp only at *)
  all_goals try exact h2
  rw [Nat.shiftRight_eq_div_pow] at hc
  rw [Nat.shiftLeft_eq]
  exact hN_fit.of_le (by change ¬ N / 4 < numMicro at hc; omega)

private def dirSlabsProg : ℕ × ℕ → Memory.Prog ℕ
  | (bBits, llf) => do
    let z0 ← pure 0
    if bBits = z0 then pure 0 else pure ((1 <<< llf) <<< 2)

@[simp] private theorem clientResult_dirSlabsProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (dirSlabsProg (bucketBits N, Dynamic.logLogFactor N)) =
      dirSlabsPerBucket N := by
  dsimp only [dirSlabsProg, dirSlabsPerBucket, slabScale]
  simp only [pure_bind]
  split_ifs with hb0 <;> simp only [prog_clientResult_pure, Nat.shiftLeft_eq, one_mul]
  ring

private theorem clientState_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (dirSlabsProg p) = s := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> rfl

@[simp] private theorem runClient_state_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (dirSlabsProg p))) = s :=
  clientState_dirSlabsProg p s

@[simp] private theorem memoryCost_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (dirSlabsProg p) s = 0 := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> rfl

private theorem validHistory_dirSlabsProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dirSlabsProg p)) := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> trivial

private def DirSlabsPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (bBits, llf), _ => Fits w 2 ∧ (bBits ≠ 0 → Fits w (2 ^ llf * 4))

private theorem realizesBounded_dirSlabs :
    RealizesBounded .exact dirSlabsProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      DirSlabsPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨bBits, llf⟩
    obtain ⟨h2, hfit⟩ := h
    dsimp only at *)
  all_goals try exact h2.of_le (by decide)
  have h4 := hfit hc
  simp only [Nat.shiftLeft_eq, one_mul]
  exact h4.of_le (by omega)

private def maxSlabsProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (bBits, (N, sSize)) => do
    let z0 ← pure 0
    if bBits = z0 then pure 0 else pure (N / sSize)

@[simp] private theorem clientResult_maxSlabsProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (maxSlabsProg (bucketBits N, (N, slabSize N))) =
      maxFullSlabs N := by
  dsimp only [maxSlabsProg, maxFullSlabs]; simp only [pure_bind]
  split_ifs <;> simp only [prog_clientResult_pure]

private theorem clientState_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (maxSlabsProg p) = s := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> rfl

@[simp] private theorem runClient_state_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (maxSlabsProg p))) = s :=
  clientState_maxSlabsProg p s

@[simp] private theorem memoryCost_maxSlabsProg (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (maxSlabsProg p) s = 0 := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> rfl

private theorem validHistory_maxSlabsProg {w : ℕ} (p : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (maxSlabsProg p)) := by
  rcases p with ⟨b, ⟨N, sz⟩⟩; dsimp only [maxSlabsProg]; simp only [pure_bind]
  split_ifs <;> trivial

private def MaxSlabsPre (_w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (bBits, (_N, sSize)), _ => bBits ≠ 0 → 0 < sSize

private theorem realizesBounded_maxSlabs :
    RealizesBounded .exact maxSlabsProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      MaxSlabsPre (fun _ _ => 0) := by
  realize
  rcases d with ⟨bBits, ⟨N, sSize⟩⟩
  dsimp only at *
  exact (h hc).ne'

private abbrev Tup3 := ℕ × (ℕ × ℕ)
private abbrev Tup4 := (ℕ × ℕ) × (ℕ × ℕ)

private def writeBlock3Prog : ℕ × Tup3 → Memory.Prog Unit
  | (base, (v0, (v1, v2))) => do
    Memory.write base v0
    Memory.write (base + 1) v1
    Memory.write (base + 2) v2

private def WriteBlock3Pre (w : ℕ) : ℕ × Tup3 → Memory.State → Prop
  | (base, _), s => base + 3 ≤ s.frontier ∧ Fits w (base + 2)

private theorem realizesBounded_writeBlock3 :
    RealizesBounded .exact writeBlock3Prog
      (WordEncoding.encode (α := ℕ × Tup3)) (WordEncoding.encode (α := Unit))
      WriteBlock3Pre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨base, ⟨v0, ⟨v1, v2⟩⟩⟩
    obtain ⟨_hfr, hbase2⟩ := h
    dsimp only at *)
  all_goals exact hbase2.of_le (by omega)

private theorem writeBlock3Prog_spec {w : ℕ} (base v0 v1 v2 : ℕ) {s : Memory.State}
    (hfr : base + 3 ≤ s.frontier) (hfit_end : Fits w (base + 2))
    (hv0 : Fits w v0) (hv1 : Fits w v1) (hv2 : Fits w v2) :
    let d : ℕ × Tup3 := (base, (v0, (v1, v2)))
    let prog := writeBlock3Prog d
    let s' := (Memory.spec 0).clientState s prog
    WriteBlock3Pre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (s'.mem base = v0 ∧ s'.mem (base + 1) = v1 ∧ s'.mem (base + 2) = v2) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 3) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 3 := by
  intro d prog s'
  refine ⟨⟨hfr, hfit_end⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeBlock3Prog] at hfr ⊢
    refine validHistory_write_step (by omega) hv0 ?_
    refine validHistory_write_step (by omega) hv1 ?_
    exact ⟨⟨show base + 2 < fr by omega, hv2⟩, trivial⟩
  · dsimp only [s', prog, d, writeBlock3Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
  · dsimp only [s', prog, d, writeBlock3Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.update_of_ne (show base ≠ base + 2 by omega),
        Function.update_of_ne (show base ≠ base + 1 by omega), Function.update_self]
    · rw [Function.update_of_ne (show base + 1 ≠ base + 2 by omega), Function.update_self]
    · rw [Function.update_self]
  · intro a ha
    dsimp only [s', prog, d, writeBlock3Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
    rw [Function.update_of_ne (show a ≠ base + 2 by omega),
      Function.update_of_ne (show a ≠ base + 1 by omega),
      Function.update_of_ne (show a ≠ base by omega)]
  · dsimp only [prog, d, writeBlock3Prog]
    simp only [Realization.memoryCost_bind', prog_memoryCost_write, prog_runClient_state_write]

private def writeBlock4Prog : ℕ × Tup4 → Memory.Prog Unit
  | (base, ((v0, v1), (v2, v3))) => do
    Memory.write base v0
    Memory.write (base + 1) v1
    Memory.write (base + 2) v2
    Memory.write (base + 3) v3

private def WriteBlock4Pre (w : ℕ) : ℕ × Tup4 → Memory.State → Prop
  | (base, _), s => base + 4 ≤ s.frontier ∧ Fits w (base + 3)

private theorem realizesBounded_writeBlock4 :
    RealizesBounded .exact writeBlock4Prog
      (WordEncoding.encode (α := ℕ × Tup4)) (WordEncoding.encode (α := Unit))
      WriteBlock4Pre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨base, ⟨⟨v0, v1⟩, ⟨v2, v3⟩⟩⟩
    obtain ⟨_hfr, hbase3⟩ := h
    dsimp only at *)
  all_goals exact hbase3.of_le (by omega)

private theorem writeBlock4Prog_spec {w : ℕ} (base v0 v1 v2 v3 : ℕ) {s : Memory.State}
    (hfr : base + 4 ≤ s.frontier) (hfit_end : Fits w (base + 3))
    (hv0 : Fits w v0) (hv1 : Fits w v1) (hv2 : Fits w v2) (hv3 : Fits w v3) :
    let d : ℕ × Tup4 := (base, ((v0, v1), (v2, v3)))
    let prog := writeBlock4Prog d
    let s' := (Memory.spec 0).clientState s prog
    WriteBlock4Pre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (s'.mem base = v0 ∧ s'.mem (base + 1) = v1 ∧ s'.mem (base + 2) = v2 ∧
      s'.mem (base + 3) = v3) ∧
    (∀ a, ¬(base ≤ a ∧ a < base + 4) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 4 := by
  intro d prog s'
  refine ⟨⟨hfr, hfit_end⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeBlock4Prog] at hfr ⊢
    refine validHistory_write_step (by omega) hv0 ?_
    refine validHistory_write_step (by omega) hv1 ?_
    refine validHistory_write_step (by omega) hv2 ?_
    exact ⟨⟨show base + 3 < fr by omega, hv3⟩, trivial⟩
  · dsimp only [s', prog, d, writeBlock4Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
  · dsimp only [s', prog, d, writeBlock4Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (show base ≠ base + 3 by omega),
        Function.update_of_ne (show base ≠ base + 2 by omega),
        Function.update_of_ne (show base ≠ base + 1 by omega), Function.update_self]
    · rw [Function.update_of_ne (show base + 1 ≠ base + 3 by omega),
        Function.update_of_ne (show base + 1 ≠ base + 2 by omega), Function.update_self]
    · rw [Function.update_of_ne (show base + 2 ≠ base + 3 by omega), Function.update_self]
    · rw [Function.update_self]
  · intro a ha
    dsimp only [s', prog, d, writeBlock4Prog, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_runClient_state_write]
    rw [Function.update_of_ne (show a ≠ base + 3 by omega),
      Function.update_of_ne (show a ≠ base + 2 by omega),
      Function.update_of_ne (show a ≠ base + 1 by omega),
      Function.update_of_ne (show a ≠ base by omega)]
  · dsimp only [prog, d, writeBlock4Prog]
    simp only [Realization.memoryCost_bind', prog_memoryCost_write, prog_runClient_state_write]

private theorem eight_le_of_fits_225 {w : ℕ} (h225 : Fits w 225) : 8 ≤ w := by
  by_contra hlt8
  have hw7 : w ≤ 7 := by omega
  have hle128 : 2 ^ w ≤ 128 := (Nat.pow_le_pow_right two_pos hw7).trans (by decide)
  have hlt : 225 < 2 ^ w := h225
  omega

/-- Pure arithmetic invariants for `computeHashCoreProg` and `writeHashParamsSubProg`. -/
private theorem computeHashCore_arith {w U N dstMetaBase : ℕ}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let B := reducedTargetBits (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let c := reducedChunkBits t
    8 ≤ w ∧ epochQBits U N ≤ w ∧ totalMicroBits N ≤ w ∧ Nat.log 2 N < w ∧
    2 * c < w ∧ B ≤ 3 * Nat.log 2 N + 3 ∧ 2 * c ≤ N + 8 ∧
    Fits w (B + 2) ∧ Fits w (3 ^ (t - 3)) ∧ Fits w (3 ^ min t 3) ∧
    Fits w (min (2 * c) (Nat.log 2 (w / (2 * c))) + 1) := by
  intro B t c
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hw8 : 8 ≤ w := eight_le_of_fits_225 h225
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hw0_le : epochQBits U N ≤ w := qBits_le_of_le_pow hw hU.le
  have hb'_eq : totalMicroBits N = Nat.log 2 N := totalMicroBits_eq_log N
  have hlogN_lt : Nat.log 2 N < w := by
    have hpow := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hN_lt : N < 2 ^ w := hU.of_le hNU
    by_contra hge
    have : 2 ^ w ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos (by omega)
    omega
  have hb'_le : totalMicroBits N ≤ w := by rw [hb'_eq]; omega
  have hfit_hash : Fits w ((dstMetaBase + epochHdrWords) + epochHashSpace U w N) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega)
  have hc_le : 2 * c ≤ w := two_mul_reducedChunkBits_le hw0_le hb'_le (by omega)
  have hc_lt : 2 * c < w := ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space hc_le hfit_hash
  have hB_le : B ≤ 3 * Nat.log 2 N + 3 := by
    dsimp only [B, reducedTargetBits, epochHashB]
    rw [totalMicroBits_eq_log]
    have h1 : min (epochQBits U N) (3 * (Nat.log 2 N + 1)) ≤ 3 * Nat.log 2 N + 3 :=
      (Nat.min_le_right _ _).trans (by omega)
    exact max_le h1 (by omega)
  have hB2_fit : Fits w (B + 2) := by
    have h3w_fit : Fits w (3 * w + 5) := by
      change 3 * w + 5 < 2 ^ w
      have hind : ∀ k, 8 ≤ k → 3 * k + 5 < 2 ^ k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          rcases eq_or_ne k 7 with rfl | _
          · decide
          · have hk8 := ih (by omega); rw [pow_succ']; omega
      exact hind w hw8
    exact h3w_fit.of_le (by omega)
  have hc_fit : Fits w (3 ^ (t - 3)) := hw_fit.of_le (show c ≤ w by omega)
  have hl0_fit : Fits w (3 ^ min t 3) := h225.of_le ((reducedHalfLimbs_le t).trans (by decide))
  have hp_fit : Fits w (min (2 * c) (Nat.log 2 (w / (2 * c))) + 1) :=
    hw_fit.of_le (by
      have := Nat.min_le_left (2 * c) (Nat.log 2 (w / (2 * c))); omega)
  have h2c_le : 2 * c ≤ N + 8 := by
    have hpow := two_pow_two_mul_reducedChunkBits_hash_le U N
    change 2 ^ (2 * c) ≤ 8 + N at hpow
    have hlt := @Nat.lt_two_pow_self (2 * c)
    omega
  exact ⟨hw8, hw0_le, hb'_le, hlogN_lt, hc_lt, hB_le, h2c_le, hB2_fit, hc_fit, hl0_fit, hp_fit⟩

private theorem fits_three_mul_w_add_five {w : ℕ} (h225 : Fits w 225) : Fits w (3 * w + 5) := by
  have hw8 : 8 ≤ w := eight_le_of_fits_225 h225
  change 3 * w + 5 < 2 ^ w
  have hind : ∀ k, 8 ≤ k → 3 * k + 5 < 2 ^ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_ne k 7 with rfl | _
      · decide
      · have hk8 := ih (by omega); rw [pow_succ']; omega
  exact hind w hw8

/-- Step 1 of `computeHashCoreProg`: compute `(w0, (minW0, t))` from `(hdrBase, qBitsVal, logN)`. -/
private def computeHashTargetProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (hdrBase, (qBitsVal, logN)) => do
    let w0 ← maxNatProg (qBitsVal, 1)
    let minW0 ← minNatProg (w0, (logN + 1) * 3)
    let maxB' ← maxNatProg (logN, 1)
    let targB ← maxNatProg (minW0, maxB')
    let t ← trinomProg (hdrBase, targB)
    pure (w0, (minW0, t))

private def ComputeHashTargetPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrBase, (qBitsVal, logN)), s =>
    qBitsVal ≤ w ∧ logN < w ∧ hdrBase < s.frontier ∧ Fits w 225

private theorem computeHashTargetProg_exec {w hdrBase qBitsVal logN : ℕ} {s : Memory.State}
    (_hq : qBitsVal ≤ w) (hlog : logN < w) (hhdr : hdrBase < s.frontier) (h225 : Fits w 225) :
    let d := (hdrBase, (qBitsVal, logN))
    let w0 := max qBitsVal 1
    let minW0 := min w0 ((logN + 1) * 3)
    let targB := max minW0 (max logN 1)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashTargetProg d)) ∧
    (Memory.spec 0).clientState s (computeHashTargetProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashTargetProg d) =
      (w0, (minW0, trinomialStepAux targB)) ∧
    memoryCost (computeHashTargetProg d) s ≤ 3 * logN + 3 := by
  intro d w0 minW0 targB
  have h3w : Fits w (3 * w + 5) := fits_three_mul_w_add_five h225
  have htarg_le : targB ≤ 3 * logN + 3 := by
    dsimp only [targB, minW0]
    have h1 : min w0 ((logN + 1) * 3) ≤ 3 * logN + 3 := (Nat.min_le_right _ _).trans (by omega)
    exact max_le h1 (by omega)
  have hB2_fit : Fits w (targB + 2) := h3w.of_le (by omega)
  obtain ⟨_, hv_tr, hc_tr, hst_tr, hres_tr⟩ :=
    trinomProg_spec (B := targB) hhdr hB2_fit (h225.of_le (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeHashTargetProg]
    rw [validHistory_bind', clientState_maxNatProg, clientResult_maxNatProg]
    refine ⟨validHistory_maxNatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_minNatProg, clientResult_minNatProg]
    refine ⟨validHistory_minNatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_maxNatProg, clientResult_maxNatProg]
    refine ⟨validHistory_maxNatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_maxNatProg, clientResult_maxNatProg]
    refine ⟨validHistory_maxNatProg _ _, ?_⟩
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (trinomProg (hdrBase, targB) >>= _))
    rw [validHistory_bind', hst_tr, hres_tr]
    exact ⟨hv_tr, True.intro⟩
  · dsimp only [d, computeHashTargetProg]
    rw [StateTransitionSpec.clientState_bind, clientState_maxNatProg, clientResult_maxNatProg,
      StateTransitionSpec.clientState_bind, clientState_minNatProg, clientResult_minNatProg,
      StateTransitionSpec.clientState_bind, clientState_maxNatProg, clientResult_maxNatProg,
      StateTransitionSpec.clientState_bind, clientState_maxNatProg, clientResult_maxNatProg]
    change (Memory.spec 0).clientState s (trinomProg (hdrBase, targB) >>= _) = s
    rw [StateTransitionSpec.clientState_bind, hst_tr, StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeHashTargetProg]
    rw [prog_clientResult_bind, clientState_maxNatProg, clientResult_maxNatProg,
      prog_clientResult_bind, clientState_minNatProg, clientResult_minNatProg,
      prog_clientResult_bind, clientState_maxNatProg, clientResult_maxNatProg,
      prog_clientResult_bind, clientState_maxNatProg, clientResult_maxNatProg]
    change (Memory.spec 0).clientResult s (trinomProg (hdrBase, targB) >>= _) = _
    rw [prog_clientResult_bind, hst_tr, hres_tr, prog_clientResult_pure]
  · dsimp only [d, computeHashTargetProg]
    rw [Realization.memoryCost_bind', memoryCost_maxNatProg, clientState_maxNatProg,
      clientResult_maxNatProg,
      Realization.memoryCost_bind', memoryCost_minNatProg, clientState_minNatProg,
      clientResult_minNatProg,
      Realization.memoryCost_bind', memoryCost_maxNatProg, clientState_maxNatProg,
      clientResult_maxNatProg,
      Realization.memoryCost_bind', memoryCost_maxNatProg, clientState_maxNatProg,
      clientResult_maxNatProg]
    change 0 + (0 + (0 + (0 + memoryCost (trinomProg (hdrBase, targB) >>= _) s))) ≤ _
    rw [Realization.memoryCost_bind', hst_tr, memoryCost_pure]
    omega

private theorem realizesBounded_computeHashTarget :
    RealizesBounded .exact computeHashTargetProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeHashTargetPre (fun _ _ => 0) := by
  have hmax := realizesBounded_maxNat
  have hmin := realizesBounded_minNat
  have htr := realizesBounded_trinom
  realize
  all_goals (
    rcases d with ⟨hdrBase, ⟨qBitsVal, logN⟩⟩
    obtain ⟨hq, hlog, hhdr, h225⟩ := h
    try dsimp only at *
    have h3w : Fits w (3 * w + 5) := fits_three_mul_w_add_five h225
    repeat rw [clientState_maxNatProg]
    repeat rw [clientResult_maxNatProg]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg])
  all_goals (
    have htarg_le : max (min (max qBitsVal 1) ((logN + 1) * 3)) (max logN 1) ≤ 3 * logN + 3 := by
      have h1 : min (max qBitsVal 1) ((logN + 1) * 3) ≤ 3 * logN + 3 :=
        (Nat.min_le_right _ _).trans (by omega)
      exact max_le h1 (by omega)
    first
    | exact ⟨hhdr, h3w.of_le (by omega), h225.of_le (by decide)⟩
    | exact h3w.of_le (by omega))

/-- Step 2 of `computeHashCoreProg`: compute `(c, (l0, p))` from any step count `t : ℕ`. -/
private def computeHashShiftsProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((hdrBase, wVal), t) => do
    let tSub3 ← subSatProg (t, 3)
    let minT3 ← minNatProg (t, 3)
    let c ← pow3Prog (hdrBase, tSub3)
    let l0 ← pow3Prog (hdrBase, minT3)
    let twoC := c + c
    let p ← log2CapProg (hdrBase, (twoC, wVal / twoC))
    pure (c, (l0, p))

private def ComputeHashShiftsPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((hdrBase, wVal), t), s =>
    0 < w ∧ wVal = w ∧ hdrBase < s.frontier ∧ 2 * reducedChunkBits t < w ∧ Fits w 225

private theorem computeHashShiftsProg_exec {w hdrBase t : ℕ} {s : Memory.State}
    (_hw : 0 < w) (hhdr : hdrBase < s.frontier) (hc_lt : 2 * reducedChunkBits t < w)
    (h225 : Fits w 225) :
    let d := ((hdrBase, w), t)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashShiftsProg d)) ∧
    (Memory.spec 0).clientState s (computeHashShiftsProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashShiftsProg d) =
      (reducedChunkBits t, (reducedHalfLimbs t, reducedPackShift t w)) ∧
    memoryCost (computeHashShiftsProg d) s ≤ t + 2 * reducedChunkBits t + 3 := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hc_fit : Fits w (3 ^ (t - 3)) :=
    hw_fit.of_le (by change reducedChunkBits t ≤ w; omega)
  have hl0_fit : Fits w (3 ^ min t 3) :=
    h225.of_le ((reducedHalfLimbs_le t).trans (by decide))
  have hp_fit : Fits w (min (2 * reducedChunkBits t)
      (Nat.log 2 (w / (2 * reducedChunkBits t))) + 1) :=
    hw_fit.of_le (by
      have := Nat.min_le_left (2 * reducedChunkBits t)
        (Nat.log 2 (w / (2 * reducedChunkBits t)))
      omega)
  obtain ⟨_, hv_p1, hc_p1, hst_p1, hres_p1⟩ := pow3Prog_spec (e := t - 3) hhdr hc_fit
  obtain ⟨_, hv_p2, hc_p2, hst_p2, hres_p2⟩ := pow3Prog_spec (e := min t 3) hhdr hl0_fit
  obtain ⟨_, hv_lg, hc_lg, hst_lg, hres_lg⟩ :=
    log2CapProg_spec (K := 2 * reducedChunkBits t) (x₀ := w / (2 * reducedChunkBits t)) hhdr
      (hw_fit.of_le (Nat.div_le_self _ _)) hp_fit
  have h2c_sum : 3 ^ (t - 3) + 3 ^ (t - 3) = 2 * reducedChunkBits t := by
    dsimp only [reducedChunkBits]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeHashShiftsProg]
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_minNatProg, clientResult_minNatProg]
    refine ⟨validHistory_minNatProg _ _, ?_⟩
    rw [validHistory_bind', hst_p1, hres_p1]; refine ⟨hv_p1, ?_⟩
    rw [validHistory_bind', hst_p2, hres_p2]; refine ⟨hv_p2, ?_⟩
    rw [h2c_sum, validHistory_bind', hst_lg]
    exact ⟨hv_lg, trivial⟩
  · dsimp only [d, computeHashShiftsProg]
    rw [StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      StateTransitionSpec.clientState_bind, clientState_minNatProg, clientResult_minNatProg,
      StateTransitionSpec.clientState_bind, hst_p1, hres_p1,
      StateTransitionSpec.clientState_bind, hst_p2, hres_p2,
      h2c_sum, StateTransitionSpec.clientState_bind, hst_lg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeHashShiftsProg]
    rw [prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      prog_clientResult_bind, clientState_minNatProg, clientResult_minNatProg,
      prog_clientResult_bind, hst_p1, hres_p1,
      prog_clientResult_bind, hst_p2, hres_p2,
      h2c_sum, prog_clientResult_bind, hst_lg, hres_lg, prog_clientResult_pure]
    rfl
  · dsimp only [d, computeHashShiftsProg]
    rw [Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg,
      Realization.memoryCost_bind', memoryCost_minNatProg, clientState_minNatProg,
      clientResult_minNatProg,
      Realization.memoryCost_bind', hst_p1, hres_p1,
      Realization.memoryCost_bind', hst_p2, hres_p2,
      h2c_sum, Realization.memoryCost_bind', hst_lg, memoryCost_pure]
    have hmin_le : min t 3 ≤ 3 := Nat.min_le_right t 3
    omega

private theorem realizesBounded_computeHashShifts :
    RealizesBounded .exact computeHashShiftsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeHashShiftsPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hmin := realizesBounded_minNat
  have hp3 := realizesBounded_pow3
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨⟨hdrBase, wVal⟩, t⟩
    obtain ⟨hw, hwVal, hhdr, hc_lt, h225⟩ := h
    subst wVal
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hc_fit : Fits w (3 ^ (t - 3)) :=
      hw_fit.of_le (by change reducedChunkBits t ≤ w; omega)
    have hl0_fit : Fits w (3 ^ min t 3) :=
      h225.of_le ((reducedHalfLimbs_le t).trans (by decide))
    have hp_fit : Fits w (min (2 * reducedChunkBits t)
        (Nat.log 2 (w / (2 * reducedChunkBits t))) + 1) :=
      hw_fit.of_le (by
        have := Nat.min_le_left (2 * reducedChunkBits t)
          (Nat.log 2 (w / (2 * reducedChunkBits t)))
        omega)
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg])
  all_goals try exact h225.of_le (by decide)
  all_goals try exact ⟨hhdr, hc_fit⟩
  all_goals (
    obtain ⟨_, _, _, hst_p1, hres_p1⟩ := pow3Prog_spec (e := t - 3) hhdr hc_fit
    repeat rw [hst_p1]
    repeat rw [hres_p1])
  all_goals try exact ⟨hhdr, hl0_fit⟩
  all_goals (
    obtain ⟨_, _, _, hst_p2, _⟩ := pow3Prog_spec (e := min t 3) hhdr hl0_fit
    have h2c_sum : 3 ^ (t - 3) + 3 ^ (t - 3) = 2 * reducedChunkBits t := by
      dsimp only [reducedChunkBits]; ring
    repeat rw [hst_p2]
    repeat rw [h2c_sum])
  all_goals try exact ⟨hhdr, hw_fit.of_le (Nat.div_le_self _ _), hp_fit⟩
  all_goals (
    have hc_pos := reducedChunkBits_pos t
    first
    | omega
    | exact hw_fit.of_le (by omega))

/-- Read-only core evaluator computing `((w0, minW0), (c, (l0, p)))` for `mkHashParams`. -/
private def computeHashCoreProg :
    (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | ((hdrBase, wVal), (qBitsVal, logN)) => do
    let (w0, (minW0, t)) ← computeHashTargetProg (hdrBase, (qBitsVal, logN))
    let (c, (l0, p)) ← computeHashShiftsProg ((hdrBase, wVal), t)
    pure ((w0, minW0), (c, (l0, p)))

private def ComputeHashCorePre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((hdrBase, wVal), (qBitsVal, logN)), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ logN = Nat.log 2 N ∧
      hdrBase < s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem computeHashCoreProg_exec {w U N hdrBase dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hhdr : hdrBase < s.frontier) (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((hdrBase, w), (quotientBits U N, Nat.log 2 N))
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashCoreProg d)) ∧
    (Memory.spec 0).clientState s (computeHashCoreProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashCoreProg d) =
      ((epochQBits U N, min (epochQBits U N) (3 * epochHashB N)),
        (reducedChunkBits t, (reducedHalfLimbs t, reducedPackShift t w))) ∧
    memoryCost (computeHashCoreProg d) s ≤ 7 * N + 20 := by
  intro d t
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  obtain ⟨_, hw0_le, _, hlogN_lt, hc_lt, hB_le, h2c_le, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  have hq_le : quotientBits U N ≤ w := (le_max_left _ 1).trans hw0_le
  obtain ⟨hv_tg, hst_tg, hres_tg, hc_tg⟩ :=
    computeHashTargetProg_exec (s := s) hq_le hlogN_lt hhdr h225
  have h3b_eq : (Nat.log 2 N + 1) * 3 = 3 * epochHashB N := by
    dsimp only [epochHashB]; rw [totalMicroBits_eq_log]; ring
  have hw0_def : max (quotientBits U N) 1 = epochQBits U N := rfl
  have hB_eq : max (min (epochQBits U N) (3 * epochHashB N)) (max (Nat.log 2 N) 1) =
      reducedTargetBits (epochQBits U N) (epochHashB N) (totalMicroBits N) := by
    dsimp only [reducedTargetBits]; rw [totalMicroBits_eq_log]
  have ht_def : trinomialStepAux
      (reducedTargetBits (epochQBits U N) (epochHashB N) (totalMicroBits N)) = t := rfl
  rw [hw0_def, h3b_eq, hB_eq, ht_def] at hres_tg
  obtain ⟨hv_sh, hst_sh, hres_sh, hc_sh⟩ :=
    computeHashShiftsProg_exec (s := s) (t := t) hw hhdr hc_lt h225
  have hlog_le_N : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
  have ht_le_N3 : t ≤ 3 * N + 3 :=
    (Cslib.DataStructure.HashFamily.WordRAM.KWise.trinomialStepAux_le _).trans
      (hB_le.trans (by omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeHashCoreProg]
    rw [validHistory_bind', hst_tg, hres_tg]; refine ⟨hv_tg, ?_⟩
    dsimp only; rw [validHistory_bind', hst_sh, hres_sh]
    exact ⟨hv_sh, True.intro⟩
  · dsimp only [d, computeHashCoreProg]
    rw [StateTransitionSpec.clientState_bind, hst_tg, hres_tg]; dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_sh, StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeHashCoreProg]
    rw [prog_clientResult_bind, hst_tg, hres_tg]; dsimp only
    rw [prog_clientResult_bind, hst_sh, hres_sh, prog_clientResult_pure]
  · dsimp only [d, computeHashCoreProg]
    rw [Realization.memoryCost_bind', hst_tg, hres_tg]; dsimp only
    rw [Realization.memoryCost_bind', hst_sh, memoryCost_pure]
    change 2 * reducedChunkBits t ≤ N + 8 at h2c_le
    omega

private theorem realizesBounded_computeHashCore :
    RealizesBounded .exact computeHashCoreProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      ComputeHashCorePre (fun _ _ => 0) := by
  have htg := realizesBounded_computeHashTarget
  have hsh := realizesBounded_computeHashShifts
  realize
  · rcases d with ⟨⟨hdrBase, wVal⟩, ⟨qBitsVal, logN⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, hfit_dst⟩ := h
    subst wVal
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    obtain ⟨_, hw0_le, _, hlogN_lt, _, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    exact ⟨(le_max_left _ 1).trans hw0_le, hlogN_lt, hhdr, h225⟩
  · rcases d with ⟨⟨hdrBase, wVal⟩, ⟨qBitsVal, logN⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, hfit_dst⟩ := h
    subst wVal
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    obtain ⟨_, hw0_le, _, hlogN_lt, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    have hq_le : quotientBits U N ≤ w := (le_max_left _ 1).trans hw0_le
    obtain ⟨_, hst_tg, hres_tg, _⟩ :=
      computeHashTargetProg_exec (s := s) hq_le hlogN_lt hhdr h225
    have h3b_eq : (Nat.log 2 N + 1) * 3 = 3 * epochHashB N := by
      dsimp only [epochHashB]; rw [totalMicroBits_eq_log]; ring
    have hw0_def : max (quotientBits U N) 1 = epochQBits U N := rfl
    have hB_eq : max (min (epochQBits U N) (3 * epochHashB N)) (max (Nat.log 2 N) 1) =
        reducedTargetBits (epochQBits U N) (epochHashB N) (totalMicroBits N) := by
      dsimp only [reducedTargetBits]; rw [totalMicroBits_eq_log]
    rw [hst_tg, hres_tg, hw0_def, h3b_eq, hB_eq]; dsimp only
    exact ⟨hw, rfl, hhdr, hc_lt, h225⟩

/-- Write words `0..11` of `mkHashParams` at `[hpBase, +12)` and return `hSpace`. -/
private def writeHashParamsLoProg : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((hpBase, w0), (minW0, c)), (l0, p)) => do
    let botW := l0 * 6
    let seedW := 1 + botW
    let hSpace := seedW + (1 <<< (c + c - p))
    let m := w0 - 1
    let h := m >>> 1
    writeBlock4Prog (hpBase, ((hSpace, seedW), (botW, (1 <<< m) - 1)))
    writeBlock4Prog (hpBase + 4,
      ((h, (1 <<< h) - 1), ((1 <<< (m - h)) - 1, (1 <<< (m - (h + h))) - 1)))
    writeBlock4Prog (hpBase + 8, ((w0 - minW0, c), ((1 <<< c) - 1, c + c)))
    pure hSpace

private def WriteHashParamsLoPre (w : ℕ) :
    ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((hpBase, w0), (minW0, c)), (l0, p)), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      hpBase = dstMetaBase + 8 ∧ w0 = epochQBits U N ∧
      minW0 = min (epochQBits U N) (3 * epochHashB N) ∧
      c = reducedChunkBits
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      l0 = reducedHalfLimbs
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      p = reducedPackShift
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) w ∧
      dstMetaBase + 27 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeHashParamsLoProg_spec {w U N dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let d := (((dstMetaBase + 8, epochQBits U N),
      (min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t)),
      (reducedHalfLimbs t, reducedPackShift t w))
    let prog := writeHashParamsLoProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteHashParamsLoPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = epochHashSpace U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 12),
      s'.mem (dstMetaBase + 8 + j) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 8 ≤ a ∧ a < dstMetaBase + 20) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 12 := by
  intro t d prog s'
  obtain ⟨_, hw0_le, hb'_le, _, hc_lt, _, _, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  have hfit_hash : Fits w ((dstMetaBase + epochHdrWords) + epochHashSpace U w N) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega)
  have hfit_scr : Fits w (dstMetaBase + offScratch + scratchWords) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
        offScratch scratchWords; omega)
  have hfit27 : Fits w (dstMetaBase + 27) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  have hhp := fits_mkHashParams (k := 3) (qBits_pos U N) hw0_le hb'_le hc_lt hfit_hash hfit_scr
  set hp := mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
  have heq_sp : (1 + reducedHalfLimbs t * 6) +
      (1 <<< (reducedChunkBits t + reducedChunkBits t - reducedPackShift t w)) =
      epochHashSpace U w N := by
    dsimp only [epochHashSpace, ReducedKWise.space, ReducedKWise.seedWords,
      ReducedKWise.tableWords, reducedTableWords, reducedLimbCount]
    rw [Nat.shiftLeft_eq, one_mul, ← two_mul]; ring
  have heq0 : epochHashSpace U w N = hp 0 := by
    change epochHashSpace U w N = hpSpace hp; rw [hpSpace_mk]
  have heq1 : 1 + reducedHalfLimbs t * 6 = hp 1 := by
    change _ = hpSeedWords hp
    rw [hpSeedWords_mk]; dsimp only [ReducedKWise.seedWords, reducedLimbCount]; ring
  have heq2 : reducedHalfLimbs t * 6 = hp 2 := by
    change _ = hpBotWords hp; rw [hpBotWords_mk]; dsimp only [reducedLimbCount]; ring
  have heq3 : (1 <<< (epochQBits U N - 1)) - 1 = hp 3 := by
    change _ = hpMaskM hp; rw [hpMaskM_mk, Nat.shiftLeft_eq, one_mul]
  have heq4 : (epochQBits U N - 1) >>> 1 = hp 4 := by
    change _ = hpHalfM hp; rw [hpHalfM_mk, Nat.shiftRight_eq_div_pow, pow_one]
  have heq5 : (1 <<< ((epochQBits U N - 1) >>> 1)) - 1 = hp 5 := by
    change _ = hpMaskH hp
    rw [hpMaskH_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul]
  have heq6 : (1 <<< ((epochQBits U N - 1) - ((epochQBits U N - 1) >>> 1))) - 1 = hp 6 := by
    change _ = hpMaskMH hp
    rw [hpMaskMH_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul]
  have heq7 : (1 <<< ((epochQBits U N - 1) -
      (((epochQBits U N - 1) >>> 1) + ((epochQBits U N - 1) >>> 1)))) - 1 = hp 7 := by
    change _ = hpMaskM2H hp
    rw [hpMaskM2H_mk, Nat.shiftRight_eq_div_pow, pow_one, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq8 : epochQBits U N - min (epochQBits U N) (3 * epochHashB N) = hp 8 := by
    change _ = hpRemShift hp; rw [hpRemShift_mk]
  have heq9 : reducedChunkBits t = hp 9 := by
    change _ = hpC hp; rw [hpC_mk]
  have heq10 : (1 <<< reducedChunkBits t) - 1 = hp 10 := by
    change _ = hpMaskC hp; rw [hpMaskC_mk, Nat.shiftLeft_eq, one_mul]
  have heq11 : reducedChunkBits t + reducedChunkBits t = hp 11 := by
    change _ = hpTwoC hp; rw [hpTwoC_mk]; ring
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8) (hp 0) (hp 1) (hp 2) (hp 3) (s := s)
      (by omega) (hfit27.of_le (by omega)) (hhp 0) (hhp 1) (hhp 2) (hhp 3)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 8, ((hp 0, hp 1), (hp 2, hp 3))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8 + 4) (hp 4) (hp 5) (hp 6) (hp 7) (s := s1)
      (by omega) (hfit27.of_le (by omega)) (hhp 4) (hhp 5) (hhp 6) (hhp 7)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock4Prog (dstMetaBase + 8 + 4, ((hp 4, hp 5), (hp 6, hp 7))))
  obtain ⟨_, hv2, hfr2, hm2, hframe2, hc2⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8 + 8) (hp 8) (hp 9) (hp 10) (hp 11) (s := s2)
      (by omega) (hfit27.of_le (by omega)) (hhp 8) (hhp 9) (hhp 10) (hhp 11)
  set s3 := (Memory.spec 0).clientState s2
    (writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 8,
      (((1 + reducedHalfLimbs t * 6) +
        (1 <<< (reducedChunkBits t + reducedChunkBits t - reducedPackShift t w)),
        1 + reducedHalfLimbs t * 6),
       (reducedHalfLimbs t * 6, (1 <<< (epochQBits U N - 1)) - 1))) =
      writeBlock4Prog (dstMetaBase + 8, ((hp 0, hp 1), (hp 2, hp 3))) := by
    rw [heq_sp, heq0, heq1, heq2, heq3]
  have hb1_eq : writeBlock4Prog (dstMetaBase + 8 + 4,
      (((epochQBits U N - 1) >>> 1, (1 <<< ((epochQBits U N - 1) >>> 1)) - 1),
       ((1 <<< ((epochQBits U N - 1) - ((epochQBits U N - 1) >>> 1))) - 1,
        (1 <<< ((epochQBits U N - 1) -
          (((epochQBits U N - 1) >>> 1) + ((epochQBits U N - 1) >>> 1)))) - 1))) =
      writeBlock4Prog (dstMetaBase + 8 + 4, ((hp 4, hp 5), (hp 6, hp 7))) := by
    rw [heq7, heq6, heq5, heq4]
  have hb2_eq : writeBlock4Prog (dstMetaBase + 8 + 8,
      ((epochQBits U N - min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t),
       ((1 <<< reducedChunkBits t) - 1, reducedChunkBits t + reducedChunkBits t))) =
      writeBlock4Prog (dstMetaBase + 8 + 8, ((hp 8, hp 9), (hp 10, hp 11))) := by
    rw [heq11, heq10, heq8, heq9]
  have hs'_eq : s' = s3 := by
    dsimp only [s', prog, d, writeHashParamsLoProg]
    rw [hb0_eq, hb1_eq, hb2_eq, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeHashParamsLoProg]
    rw [hb0_eq, hb1_eq, hb2_eq, validHistory_bind']
    refine ⟨hv0, ?_⟩
    rw [validHistory_bind']; refine ⟨hv1, ?_⟩
    rw [validHistory_bind']; exact ⟨hv2, trivial⟩
  · dsimp only [prog, d, writeHashParamsLoProg]
    rw [hb0_eq, hb1_eq, hb2_eq, prog_clientResult_bind, prog_clientResult_bind,
      prog_clientResult_bind, prog_clientResult_pure]
    exact heq_sp
  · rw [hs'_eq, hfr2, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    obtain ⟨m20, m21, m22, m23⟩ := hm2
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Nat.add_zero, hframe2 _ (by omega), hframe1 _ (by omega)]; exact m00
    · rw [hframe2 _ (by omega), hframe1 _ (by omega)]; exact m01
    · rw [hframe2 _ (by omega), hframe1 _ (by omega)]; exact m02
    · rw [hframe2 _ (by omega), hframe1 _ (by omega)]; exact m03
    · rw [hframe2 _ (by omega)]; exact m10
    · rw [show dstMetaBase + 8 + 5 = dstMetaBase + 8 + 4 + 1 by omega, hframe2 _ (by omega)]
      exact m11
    · rw [show dstMetaBase + 8 + 6 = dstMetaBase + 8 + 4 + 2 by omega, hframe2 _ (by omega)]
      exact m12
    · rw [show dstMetaBase + 8 + 7 = dstMetaBase + 8 + 4 + 3 by omega, hframe2 _ (by omega)]
      exact m13
    · exact m20
    · rw [show dstMetaBase + 8 + 9 = dstMetaBase + 8 + 8 + 1 by omega]; exact m21
    · rw [show dstMetaBase + 8 + 10 = dstMetaBase + 8 + 8 + 2 by omega]; exact m22
    · rw [show dstMetaBase + 8 + 11 = dstMetaBase + 8 + 8 + 3 by omega]; exact m23
  · intro a ha
    rw [hs'_eq, hframe2 a (by omega), hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeHashParamsLoProg]
    rw [hb0_eq, hb1_eq, hb2_eq, Realization.memoryCost_bind', Realization.memoryCost_bind',
      Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeBlock4Prog _) s +
      (memoryCost (writeBlock4Prog _) s1 + (memoryCost (writeBlock4Prog _) s2 + 0)) = 12
    rw [hc0, hc1, hc2]

private theorem realizesBounded_writeHashParamsLo :
    RealizesBounded .exact writeHashParamsLoProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      WriteHashParamsLoPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨hpBase, w0⟩, ⟨minW0, c⟩⟩, ⟨l0, p⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    obtain ⟨_, hw0_le, _, _, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    have hfit_hash : Fits w ((dstMetaBase + epochHdrWords) + epochHashSpace U w N) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega)
    have hfit27 : Fits w (dstMetaBase + 27) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit27.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    change 2 * reducedChunkBits t < w at hc_lt
    have hpow2c : Fits w (2 ^ (2 * reducedChunkBits t)) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hpowm : Fits w (2 ^ (epochQBits U N - 1)) :=
      Nat.pow_lt_pow_right one_lt_two (by have := qBits_pos U N; omega)
    have hl0_le : reducedHalfLimbs t ≤ 27 := reducedHalfLimbs_le t
    have hspace_fit : Fits w (epochHashSpace U w N) := hfit_hash.of_le (by omega)
    have hp_le : reducedPackShift t w ≤ reducedChunkBits t + reducedChunkBits t := by
      dsimp only [reducedPackShift]
      have := Nat.min_le_left (2 * reducedChunkBits t) (Nat.log 2 (w / (2 * reducedChunkBits t)))
      omega
    have h2c_eq : reducedChunkBits t + reducedChunkBits t = 2 * reducedChunkBits t := by ring
    have h6l_eq : reducedHalfLimbs t * 6 = 3 * reducedLimbCount t := by
      dsimp only [reducedLimbCount]; ring
    try rw [Nat.shiftLeft_eq, one_mul]
    try rw [Nat.shiftRight_eq_div_pow, pow_one]
    first
    | exact hp_le
    | exact qBits_pos U N
    | exact Nat.min_le_left _ _
    | exact Nat.div_le_self _ _
    | exact (by omega :
        (epochQBits U N - 1) / 2 + (epochQBits U N - 1) / 2 ≤ epochQBits U N - 1)
    | exact hw_fit.of_le (by omega)
    | exact h225.of_le (by omega)
    | exact hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega))
    | exact hpowm.of_le (Nat.pow_le_pow_right two_pos (by omega))
    | (rw [h2c_eq]
       exact hspace_fit.of_le (by
         change 1 + reducedHalfLimbs t * 6 +
           2 ^ (2 * reducedChunkBits t - reducedPackShift t w) ≤
           (1 + 3 * (2 * reducedHalfLimbs t)) +
           2 ^ (2 * reducedChunkBits t - reducedPackShift t w)
         omega))
    | (refine ⟨?_, hfit27.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Write words `12..18` of `mkHashParams` at `[hpBase + 12, +7)`. -/
private def writeHashParamsHiProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((hpBase, c), (l0, (p, logN))) => do
    let pow2C := 1 <<< (c + c)
    writeBlock4Prog (hpBase + 12, ((pow2C, pow2C - 1), (p, (1 <<< p) - 1)))
    writeBlock3Prog (hpBase + 16, (l0, (3, logN)))

private def WriteHashParamsHiPre (w : ℕ) : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((hpBase, c), (l0, (p, logN))), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      hpBase = dstMetaBase + 8 ∧
      c = reducedChunkBits
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      l0 = reducedHalfLimbs
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) ∧
      p = reducedPackShift
        (reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)) w ∧
      logN = Nat.log 2 N ∧
      dstMetaBase + 27 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeHashParamsHiProg_spec {w U N dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let d := ((dstMetaBase + 8, reducedChunkBits t),
      (reducedHalfLimbs t, (reducedPackShift t w, Nat.log 2 N)))
    let prog := writeHashParamsHiProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteHashParamsHiPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 7),
      s'.mem (dstMetaBase + 20 + j) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
          ⟨12 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 20 ≤ a ∧ a < dstMetaBase + 27) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 7 := by
  intro t d prog s'
  obtain ⟨_, hw0_le, hb'_le, _, hc_lt, _, _, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  have hfit_hash : Fits w ((dstMetaBase + epochHdrWords) + epochHashSpace U w N) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM; omega)
  have hfit_scr : Fits w (dstMetaBase + offScratch + scratchWords) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
        offScratch scratchWords; omega)
  have hfit27 : Fits w (dstMetaBase + 27) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  have hhp := fits_mkHashParams (k := 3) (qBits_pos U N) hw0_le hb'_le hc_lt hfit_hash hfit_scr
  set hp := mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3
  have heq12 : 1 <<< (reducedChunkBits t + reducedChunkBits t) = hp 12 := by
    change _ = hpPow2C hp; rw [hpPow2C_mk, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq13 : (1 <<< (reducedChunkBits t + reducedChunkBits t)) - 1 = hp 13 := by
    change _ = hpMask2C hp; rw [hpMask2C_mk, Nat.shiftLeft_eq, one_mul, two_mul]
  have heq14 : reducedPackShift t w = hp 14 := by
    change _ = hpP hp; rw [hpP_mk]
  have heq15 : (1 <<< reducedPackShift t w) - 1 = hp 15 := by
    change _ = hpMaskP hp; rw [hpMaskP_mk, Nat.shiftLeft_eq, one_mul]
  have heq16 : reducedHalfLimbs t = hp 16 := by
    change _ = hpL0 hp; rw [hpL0_mk]
  have heq17 : 3 = hp 17 := by
    change _ = hpK hp; rw [hpK_mk]
  have heq18 : Nat.log 2 N = hp 18 := by
    change _ = hpB' hp; rw [hpB'_mk]; exact (totalMicroBits_eq_log N).symm
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 8 + 12) (hp 12) (hp 13) (hp 14) (hp 15) (s := s)
      (by omega) (hfit27.of_le (by omega)) (hhp 12) (hhp 13) (hhp 14) (hhp 15)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 8 + 12, ((hp 12, hp 13), (hp 14, hp 15))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock3Prog_spec (dstMetaBase + 8 + 16) (hp 16) (hp 17) (hp 18) (s := s1)
      (by omega) (hfit27.of_le (by omega)) (hhp 16) (hhp 17) (hhp 18)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock3Prog (dstMetaBase + 8 + 16, (hp 16, (hp 17, hp 18))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 8 + 12,
      ((1 <<< (reducedChunkBits t + reducedChunkBits t),
        (1 <<< (reducedChunkBits t + reducedChunkBits t)) - 1),
       (reducedPackShift t w, (1 <<< reducedPackShift t w) - 1))) =
      writeBlock4Prog (dstMetaBase + 8 + 12, ((hp 12, hp 13), (hp 14, hp 15))) := by
    rw [heq13, heq12, heq15, heq14]
  have hb1_eq : writeBlock3Prog (dstMetaBase + 8 + 16,
      (reducedHalfLimbs t, (3, Nat.log 2 N))) =
      writeBlock3Prog (dstMetaBase + 8 + 16, (hp 16, (hp 17, hp 18))) := by
    rw [heq16, heq17, heq18]
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, StateTransitionSpec.clientState_bind]
  refine ⟨⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, validHistory_bind']
    exact ⟨hv0, hv1⟩
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 20 + 0 = dstMetaBase + 8 + 12 by omega, hframe1 _ (by omega)]
      exact m00
    · rw [show dstMetaBase + 20 + 1 = dstMetaBase + 8 + 12 + 1 by omega, hframe1 _ (by omega)]
      exact m01
    · rw [show dstMetaBase + 20 + 2 = dstMetaBase + 8 + 12 + 2 by omega, hframe1 _ (by omega)]
      exact m02
    · rw [show dstMetaBase + 20 + 3 = dstMetaBase + 8 + 12 + 3 by omega, hframe1 _ (by omega)]
      exact m03
    · rw [show dstMetaBase + 20 + 4 = dstMetaBase + 8 + 16 by omega]; exact m10
    · rw [show dstMetaBase + 20 + 5 = dstMetaBase + 8 + 16 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 20 + 6 = dstMetaBase + 8 + 16 + 2 by omega]; exact m12
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeHashParamsHiProg]
    rw [hb0_eq, hb1_eq, Realization.memoryCost_bind']
    change memoryCost (writeBlock4Prog _) s + memoryCost (writeBlock3Prog _) s1 = 7
    rw [hc0, hc1]

private theorem realizesBounded_writeHashParamsHi :
    RealizesBounded .exact writeHashParamsHiProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      WriteHashParamsHiPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  have hb3 := realizesBounded_writeBlock3
  realize
  all_goals (
    rcases d with ⟨⟨hpBase, c⟩, ⟨l0, ⟨p, logN⟩⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    obtain ⟨_, _, _, _, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    have hfit27 : Fits w (dstMetaBase + 27) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit27.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    change 2 * reducedChunkBits t < w at hc_lt
    have hpow2c : Fits w (2 ^ (2 * reducedChunkBits t)) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hp_le : reducedPackShift t w ≤ 2 * reducedChunkBits t := reducedPackShift_le t w
    try rw [Nat.shiftLeft_eq, one_mul]
    first
    | exact hw_fit.of_le (by omega)
    | (rw [← two_mul]; exact hpow2c)
    | exact hpow2c.of_le (Nat.pow_le_pow_right two_pos hp_le)
    | (refine ⟨?_, hfit27.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Compute and write the 19-word `mkHashParams` block at `[dstMetaBase + 8, +19)`, returning
`epochHashSpace U w N`. -/
private def writeHashParamsSubProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | ((hdrBase, dstMetaBase), (wVal, (qBitsVal, logN))) => do
    let ((w0, minW0), (c, (l0, p))) ←
      computeHashCoreProg ((hdrBase, wVal), (qBitsVal, logN))
    let hpBase := dstMetaBase + 8
    let hSpace ← writeHashParamsLoProg (((hpBase, w0), (minW0, c)), (l0, p))
    writeHashParamsHiProg ((hpBase, c), (l0, (p, logN)))
    pure hSpace

private def WriteHashParamsSubPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((hdrBase, dstMetaBase), (wVal, (qBitsVal, logN))), s =>
    ∃ U N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ logN = Nat.log 2 N ∧
      hdrBase < s.frontier ∧ dstMetaBase + 27 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

private theorem writeHashParamsSubProg_props {w U N hdrBase dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hhdr : hdrBase < s.frontier) (h27 : dstMetaBase + 27 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((hdrBase, dstMetaBase), (w, (quotientBits U N, Nat.log 2 N)))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeHashParamsSubProg d)) ∧
    (Memory.spec 0).clientResult s (writeHashParamsSubProg d) = epochHashSpace U w N ∧
    ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).frontier = s.frontier ∧
    (∀ i : Fin 19,
      ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).mem
        (dstMetaBase + offHashParams + i.val) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i) ∧
    (∀ a, ¬(dstMetaBase + offHashParams ≤ a ∧ a < dstMetaBase + offCompParams) →
      ((Memory.spec 0).clientState s (writeHashParamsSubProg d)).mem a = s.mem a) ∧
    memoryCost (writeHashParamsSubProg d) s ≤ 7 * N + 39 := by
  intro d
  obtain ⟨hv_core, hst_core, hres_core, hc_core⟩ :=
    computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
  obtain ⟨_, hv_lo, hres_lo, hfr_lo, hmem_lo, hframe_lo, hc_lo⟩ :=
    writeHashParamsLoProg_spec (s := s) hw hN hNU hU h27 hfit_dst
  set t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
  set d_lo := (((dstMetaBase + 8, epochQBits U N),
    (min (epochQBits U N) (3 * epochHashB N), reducedChunkBits t)),
    (reducedHalfLimbs t, reducedPackShift t w))
  set s1 := (Memory.spec 0).clientState s (writeHashParamsLoProg d_lo)
  obtain ⟨_, hv_hi, hfr_hi, hmem_hi, hframe_hi, hc_hi⟩ :=
    writeHashParamsHiProg_spec (s := s1) hw hN hNU hU (hfr_lo.symm ▸ h27) hfit_dst
  set d_hi := ((dstMetaBase + 8, reducedChunkBits t),
    (reducedHalfLimbs t, (reducedPackShift t w, Nat.log 2 N)))
  set s2 := (Memory.spec 0).clientState s1 (writeHashParamsHiProg d_hi)
  have hs_final : (Memory.spec 0).clientState s (writeHashParamsSubProg d) = s2 := by
    dsimp only [d, writeHashParamsSubProg]
    rw [StateTransitionSpec.clientState_bind, hst_core, hres_core]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hres_lo, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d, writeHashParamsSubProg]
    rw [validHistory_bind', hst_core, hres_core]
    refine ⟨hv_core, ?_⟩
    dsimp only; rw [validHistory_bind']
    refine ⟨hv_lo, ?_⟩
    rw [validHistory_bind']; exact ⟨hv_hi, trivial⟩
  · dsimp only [d, writeHashParamsSubProg]
    rw [prog_clientResult_bind, hst_core, hres_core]
    dsimp only
    rw [prog_clientResult_bind, hres_lo, prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs_final, hfr_hi, hfr_lo]
  · intro ⟨j, hj⟩
    rw [hs_final]
    dsimp only [offHashParams]
    by_cases hj12 : j < 12
    · rw [hframe_hi _ (by omega)]
      exact hmem_lo j hj12
    · have hk : j - 12 < 7 := by omega
      have hhi := hmem_hi (j - 12) hk
      rw [show dstMetaBase + 20 + (j - 12) = dstMetaBase + 8 + j by omega] at hhi
      exact hhi.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
  · intro a ha
    rw [hs_final]
    unfold offHashParams offCompParams at ha
    rw [hframe_hi a (by omega), hframe_lo a (by omega)]
  · dsimp only [d, writeHashParamsSubProg]
    rw [Realization.memoryCost_bind', hst_core, hres_core]
    dsimp only
    rw [Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (computeHashCoreProg _) s +
      (memoryCost (writeHashParamsLoProg d_lo) s +
        (memoryCost (writeHashParamsHiProg d_hi) s1 + 0)) ≤ _
    omega

private theorem realizesBounded_writeHashParamsSub :
    RealizesBounded .exact writeHashParamsSubProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (WordEncoding.encode (α := ℕ))
      WriteHashParamsSubPre (fun _ _ => 0) := by
  have hcore := realizesBounded_computeHashCore
  have hlo := realizesBounded_writeHashParamsLo
  have hhi := realizesBounded_writeHashParamsHi
  realize
  all_goals (
    rcases d with ⟨⟨hdrBase, dstMetaBase⟩, ⟨wVal, ⟨qBitsVal, logN⟩⟩⟩
    obtain ⟨U, N, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, h27, hfit_dst⟩ := h
    subst wVal
    dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hfit27 : Fits w (dstMetaBase + 27) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact hfit27.of_le (by omega)
  · exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, hhdr, hfit_dst⟩
  · obtain ⟨_, hst_core, hres_core, _⟩ :=
      computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
    rw [hst_core, hres_core]; dsimp only
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, h27, hfit_dst⟩
  · obtain ⟨_, hst_core, hres_core, _⟩ :=
      computeHashCoreProg_exec (s := s) hw hN hNU hU hhdr hfit_dst
    rw [hst_core, hres_core]; dsimp only
    obtain ⟨_, _, _, hfr_lo, _, _, _⟩ :=
      writeHashParamsLoProg_spec (s := s) hw hN hNU hU h27 hfit_dst
    exact ⟨U, N, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl,
      by rw [hfr_lo]; exact h27, hfit_dst⟩

/-- Copy the 5 static root-header words `[U - 1, V - 1, w, keyBits U, valBits V]` from
`[srcHdrBase, +5)` and write the 8-word root header at `[dstMetaBase, +8)`, returning
`(w, (keyBits U, valBits V))`. -/
private def writeRootHdrSubProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))) => do
    let uSub1 ← Memory.read srcHdrBase
    let vSub1 ← Memory.read (srcHdrBase + 1)
    let wVal ← Memory.read (srcHdrBase + 2)
    let kBits ← Memory.read (srcHdrBase + 3)
    let vBits ← Memory.read (srcHdrBase + 4)
    Memory.write dstMetaBase uSub1
    Memory.write (dstMetaBase + 1) vSub1
    Memory.write (dstMetaBase + 2) wVal
    Memory.write (dstMetaBase + 3) kBits
    Memory.write (dstMetaBase + 4) vBits
    Memory.write (dstMetaBase + 5) N
    Memory.write (dstMetaBase + 6) n_cur
    Memory.write (dstMetaBase + 7) n_init_new
    pure (wVal, (kBits, vBits))

private def WriteRootHdrSubPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))), s =>
    srcHdrBase + 5 ≤ s.frontier ∧ dstMetaBase + 8 ≤ s.frontier ∧
    Fits w (s.mem srcHdrBase) ∧ Fits w (s.mem (srcHdrBase + 1)) ∧
    Fits w (s.mem (srcHdrBase + 2)) ∧ Fits w (s.mem (srcHdrBase + 3)) ∧
    Fits w (s.mem (srcHdrBase + 4)) ∧
    Fits w N ∧ Fits w n_cur ∧ Fits w n_init_new ∧ Fits w 7

private theorem realizesBounded_writeRootHdrSub :
    RealizesBounded .exact writeRootHdrSubProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      WriteRootHdrSubPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨srcHdrBase, dstMetaBase⟩, ⟨N, ⟨n_cur, n_init_new⟩⟩⟩
    obtain ⟨hsrc, hdst, hm0, hm1, hm2, hm3, hm4, hN, hnc, hni, h7⟩ := h
    dsimp only at *)
  all_goals exact hmem.1.of_le (by omega)

private theorem writeRootHdrSubProg_spec
    {w U V N_old n_old n_init_old srcHdrBase dstMetaBase N n_cur n_init_new : ℕ}
    {s : Memory.State}
    (hhdr : RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem)
    (hV : V ≤ 2 ^ w) (hN_fit : Fits w N) (hnc_fit : Fits w n_cur) (hni_fit : Fits w n_init_new)
    (h7 : Fits w 7) (hsrc_fr : srcHdrBase + 5 ≤ s.frontier)
    (hdst_fr : dstMetaBase + 8 ≤ s.frontier) :
    let d := ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let prog := writeRootHdrSubProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteRootHdrSubPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = (w, (keyBits U, valBits V)) ∧
    s'.frontier = s.frontier ∧
    RootHeaderValid U V w N n_cur n_init_new dstMetaBase s'.mem ∧
    (∀ a, ¬(dstMetaBase ≤ a ∧ a < dstMetaBase + 8) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ 13 := by
  intro d prog s'
  have hU := hhdr.fits_U
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hm0 : Fits w (s.mem srcHdrBase) := by rw [hhdr.hdr_U]; exact hU.of_le (Nat.sub_le U 1)
  have hm1 : Fits w (s.mem (srcHdrBase + 1)) := by
    rw [hhdr.hdr_V]; have := hhdr.pos_V; change V - 1 < 2 ^ w; omega
  have hm2 : Fits w (s.mem (srcHdrBase + 2)) := by rw [hhdr.hdr_w]; exact hw_fit
  have hm3 : Fits w (s.mem (srcHdrBase + 3)) := by
    rw [hhdr.hdr_keyBits]; exact hw_fit.of_le (Nat.clog_le_of_le_pow hU.le)
  have hm4 : Fits w (s.mem (srcHdrBase + 4)) := by
    rw [hhdr.hdr_valBits]; exact hw_fit.of_le (Nat.clog_le_of_le_pow hV)
  refine ⟨⟨hsrc_fr, hdst_fr, hm0, hm1, hm2, hm3, hm4, hN_fit, hnc_fit, hni_fit, h7⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeRootHdrSubProg] at hsrc_fr hdst_fr hm0 hm1 hm2 hm3 hm4 ⊢
    refine validHistory_read_step (by omega) ?_
    refine validHistory_read_step (by omega) ?_
    refine validHistory_read_step (by omega) ?_
    refine validHistory_read_step (by omega) ?_
    refine validHistory_read_step (by omega) ?_
    refine validHistory_write_step (by omega) hm0 ?_
    refine validHistory_write_step (by omega) hm1 ?_
    refine validHistory_write_step (by omega) hm2 ?_
    refine validHistory_write_step (by omega) hm3 ?_
    refine validHistory_write_step (by omega) hm4 ?_
    refine validHistory_write_step (by omega) hN_fit ?_
    refine validHistory_write_step (by omega) hnc_fit ?_
    exact ⟨⟨show dstMetaBase + 7 < fr by omega, hni_fit⟩, trivial⟩
  · dsimp only [prog, d, writeRootHdrSubProg]
    simp only [prog_clientResult_bind, prog_clientResult_read, prog_runClient_state_read,
      prog_runClient_state_write, prog_clientResult_pure,
      hhdr.hdr_w, hhdr.hdr_keyBits, hhdr.hdr_valBits]
  · dsimp only [s', prog, d, writeRootHdrSubProg]
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_clientResult_read, prog_runClient_state_read, prog_runClient_state_write,
      prog_runClient_state_pure]
  · dsimp only [s', prog, d, writeRootHdrSubProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind,
      prog_clientResult_read, prog_runClient_state_read, prog_runClient_state_write,
      prog_runClient_state_pure, hhdr.hdr_U, hhdr.hdr_V, hhdr.hdr_w, hhdr.hdr_keyBits,
      hhdr.hdr_valBits]
    refine ⟨hU, hhdr.pos_U, hhdr.pos_V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 6 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 5 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 4 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 3 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 2 by omega),
        Function.update_of_ne (show dstMetaBase ≠ dstMetaBase + 1 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 6 by omega),
        Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 5 by omega),
        Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 4 by omega),
        Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 3 by omega),
        Function.update_of_ne (show dstMetaBase + 1 ≠ dstMetaBase + 2 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 2 ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase + 2 ≠ dstMetaBase + 6 by omega),
        Function.update_of_ne (show dstMetaBase + 2 ≠ dstMetaBase + 5 by omega),
        Function.update_of_ne (show dstMetaBase + 2 ≠ dstMetaBase + 4 by omega),
        Function.update_of_ne (show dstMetaBase + 2 ≠ dstMetaBase + 3 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 3 ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase + 3 ≠ dstMetaBase + 6 by omega),
        Function.update_of_ne (show dstMetaBase + 3 ≠ dstMetaBase + 5 by omega),
        Function.update_of_ne (show dstMetaBase + 3 ≠ dstMetaBase + 4 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 4 ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase + 4 ≠ dstMetaBase + 6 by omega),
        Function.update_of_ne (show dstMetaBase + 4 ≠ dstMetaBase + 5 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 5 ≠ dstMetaBase + 7 by omega),
        Function.update_of_ne (show dstMetaBase + 5 ≠ dstMetaBase + 6 by omega),
        Function.update_self]
    · rw [Function.update_of_ne (show dstMetaBase + 6 ≠ dstMetaBase + 7 by omega),
        Function.update_self]
    · rw [Function.update_self]
  · intro a ha
    dsimp only [s', prog, d, writeRootHdrSubProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_clientResult_read, prog_runClient_state_read,
      prog_runClient_state_write, prog_runClient_state_pure]
    rw [Function.update_of_ne (show a ≠ dstMetaBase + 7 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 6 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 5 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 4 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 3 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 2 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase + 1 by omega),
      Function.update_of_ne (show a ≠ dstMetaBase by omega)]
  · dsimp only [prog, d, writeRootHdrSubProg]
    simp only [Realization.memoryCost_bind', prog_memoryCost_read, prog_runClient_state_read,
      prog_memoryCost_write, prog_runClient_state_write, memoryCost_pure]
    omega

private theorem globalMetaLen_cond_eq (N : ℕ) :
    (if bucketBits N = 0 then 4
     else gmSlabMetaBase N + maxFullSlabs N * 4) =
      globalMetaLen N := by
  by_cases hb0 : bucketBits N = 0
  · simp [globalMetaLen, globalMetaVarLen, hb0]
  · rw [ite_eq_right hb0]
    have hpos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hlen := gmSlabMetaBase_add_eq_globalMetaLen hpos
    linarith

/-- Pure arithmetic bounds for `computeLogScalesProg` and `computeCompScalesProg`. -/
private theorem computeLogScales_arith {w U N : ℕ}
    (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (h225 : Fits w 225) :
    Nat.log 2 N < w ∧
    Fits w (max N 4) ∧
    2 ≤ Nat.clog 2 (max N 4) ∧
    Nat.clog 2 (max N 4) ≤ w ∧
    Nat.log 2 (max N 4 - 1) + 1 = Nat.clog 2 (max N 4) ∧
    Nat.log 2 (Nat.clog 2 (max N 4) - 1) + 1 = Dynamic.logLogFactor N ∧
    Fits w (3 * Dynamic.logLogFactor N) := by
  have hN_fit : Fits w N := hU.of_le hNU
  have hlogN_lt : Nat.log 2 N < w := by
    by_contra hge
    have : 2 ^ w ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos (by omega)
    have := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    change N < 2 ^ w at hN_fit; omega
  have hmaxN4_fit : Fits w (max N 4) := max_lt hN_fit (h225.of_le (by decide))
  have hclog1_ge2 : 2 ≤ Nat.clog 2 (max N 4) := by
    have : Nat.clog 2 4 = 2 := by decide
    rw [← this]; exact Nat.clog_mono_right 2 (le_max_right N 4)
  have hclog1_le_w : Nat.clog 2 (max N 4) ≤ w :=
    Nat.clog_le_of_le_pow (max_le hN_fit.le ((show (4 : ℕ) ≤ 225 by decide).trans h225.le))
  have hclog1_eq : Nat.log 2 (max N 4 - 1) + 1 = Nat.clog 2 (max N 4) :=
    (clog2_eq_log2_pred_add_one (lt_of_lt_of_le (by decide : 1 < 4) (le_max_right N 4))).symm
  have hllf_eq : Nat.log 2 (Nat.clog 2 (max N 4) - 1) + 1 = Dynamic.logLogFactor N :=
    (clog2_eq_log2_pred_add_one (lt_of_lt_of_le (by decide : 1 < 2) hclog1_ge2)).symm
  have hllf_le_w : Dynamic.logLogFactor N ≤ w := by
    have hlog_lt : Nat.log 2 (Nat.clog 2 (max N 4) - 1) < w :=
      (Nat.log_le_self 2 _).trans_lt (by omega)
    omega
  have h3llf_fit : Fits w (3 * Dynamic.logLogFactor N) := by
    change 3 * Dynamic.logLogFactor N < 2 ^ w
    have hw8 : 8 ≤ w := eight_le_of_fits_225 h225
    have hind : ∀ k, 8 ≤ k → 3 * k < 2 ^ k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases eq_or_ne k 7 with rfl | _
        · decide
        · have := ih (by omega); rw [pow_succ']; omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 3 hllf_le_w) (hind w hw8)
  exact ⟨hlogN_lt, hmaxN4_fit, hclog1_ge2, hclog1_le_w, hclog1_eq, hllf_eq, h3llf_fit⟩

/-- Compute `(logN, qBitsVal, llf)` from `(dstMetaBase, N, kBits)` via `log2CapProg`. -/
private def computeLogScalesProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (dstMetaBase, (N, kBits)) => do
    let logN ← log2CapProg (dstMetaBase, (N, N))
    let maxN4 ← maxNatProg (N, 4)
    let maxN4Sub1 ← subSatProg (maxN4, 1)
    let logMaxN4Sub1 ← log2CapProg (dstMetaBase, (maxN4Sub1, maxN4Sub1))
    let clogSub1 ← subSatProg (logMaxN4Sub1 + 1, 1)
    let logClogSub1 ← log2CapProg (dstMetaBase, (clogSub1, clogSub1))
    let llf := logClogSub1 + 1
    let bBits ← subSatProg (logN, llf * 3)
    let qBitsVal ← subSatProg (kBits, bBits)
    pure (logN, (qBitsVal, llf))

private def ComputeLogScalesPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (dstMetaBase, (N, kBits)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ kBits = keyBits U ∧
      dstMetaBase < s.frontier ∧ Fits w 225

private theorem computeLogScalesProg_exec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (_hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hdst_lt : dstMetaBase < s.frontier) (h225 : Fits w 225) :
    let d := (dstMetaBase, (N, keyBits U))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeLogScalesProg d)) ∧
    (Memory.spec 0).clientState s (computeLogScalesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeLogScalesProg d) =
      (Nat.log 2 N, (quotientBits U N, Dynamic.logLogFactor N)) ∧
    memoryCost (computeLogScalesProg d) s ≤ 3 * N + 6 := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hN_fit : Fits w N := hU.of_le hNU
  obtain ⟨hlogN_lt, hmaxN4_fit, _, hclog1_le_w, hclog1_eq, hllf_eq, _⟩ :=
    computeLogScales_arith hN hNU hU h225
  obtain ⟨_, hv1, hc1, hst1, hres1⟩ :=
    log2CapProg_spec (K := N) (x₀ := N) hdst_lt hN_fit
      (hw_fit.of_le (by have := Nat.min_le_right N (Nat.log 2 N); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 N)] at hres1
  obtain ⟨_, hv2, hc2, hst2, hres2⟩ :=
    log2CapProg_spec (K := max N 4 - 1) (x₀ := max N 4 - 1) hdst_lt
      (hmaxN4_fit.of_le (Nat.sub_le _ _))
      (hw_fit.of_le (by have := Nat.min_le_right (max N 4 - 1) (Nat.log 2 (max N 4 - 1)); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres2
  obtain ⟨_, hv3, hc3, hst3, hres3⟩ :=
    log2CapProg_spec (K := Nat.clog 2 (max N 4) - 1) (x₀ := Nat.clog 2 (max N 4) - 1) hdst_lt
      (hw_fit.of_le (by omega))
      (hw_fit.of_le (by
        have := Nat.min_le_right (Nat.clog 2 (max N 4) - 1)
          (Nat.log 2 (Nat.clog 2 (max N 4) - 1)); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres3
  have hclog_le_N3 : Nat.clog 2 (max N 4) - 1 ≤ N + 3 := by
    have := Nat.log_le_self 2 (max N 4 - 1); omega
  have h3llf_comm : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeLogScalesProg]
    rw [validHistory_bind', hst1, hres1]; refine ⟨hv1, ?_⟩
    rw [validHistory_bind', clientState_maxNatProg, clientResult_maxNatProg]
    refine ⟨validHistory_maxNatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', hst2, hres2, hclog1_eq]; refine ⟨hv2, ?_⟩
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', hst3, hres3]; refine ⟨hv3, ?_⟩
    rw [hllf_eq, validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_subSatProg]
    exact ⟨validHistory_subSatProg _ _, trivial⟩
  · dsimp only [d, computeLogScalesProg]
    rw [StateTransitionSpec.clientState_bind, hst1, hres1,
      StateTransitionSpec.clientState_bind, clientState_maxNatProg, clientResult_maxNatProg,
      StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      StateTransitionSpec.clientState_bind, hst2, hres2, hclog1_eq,
      StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      StateTransitionSpec.clientState_bind, hst3, hres3,
      StateTransitionSpec.clientState_bind, clientState_subSatProg,
      StateTransitionSpec.clientState_bind, clientState_subSatProg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeLogScalesProg]
    rw [prog_clientResult_bind, hst1, hres1,
      prog_clientResult_bind, clientState_maxNatProg, clientResult_maxNatProg,
      prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      prog_clientResult_bind, hst2, hres2, hclog1_eq,
      prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      prog_clientResult_bind, hst3, hres3,
      hllf_eq, h3llf_comm, prog_clientResult_bind, clientState_subSatProg,
      clientResult_subSatProg, prog_clientResult_bind, clientState_subSatProg,
      clientResult_subSatProg, prog_clientResult_pure]
    rfl
  · dsimp only [d, computeLogScalesProg]
    rw [Realization.memoryCost_bind', hst1, hres1,
      Realization.memoryCost_bind', memoryCost_maxNatProg, clientState_maxNatProg,
      clientResult_maxNatProg,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg,
      Realization.memoryCost_bind', hst2, hres2, hclog1_eq,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg,
      Realization.memoryCost_bind', hst3, hres3,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      memoryCost_pure]
    omega

private theorem realizesBounded_computeLogScales :
    RealizesBounded .exact computeLogScalesProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeLogScalesPre (fun _ _ => 0) := by
  have hmax := realizesBounded_maxNat
  have hsub := realizesBounded_subSat
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨dstMetaBase, ⟨N, kBits⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, hdst_lt, h225⟩ := h
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hN_fit : Fits w N := hU.of_le hNU
    obtain ⟨hlogN_lt, hmaxN4_fit, _, hclog1_le_w, hclog1_eq, hllf_eq, h3llf⟩ :=
      computeLogScales_arith hN hNU hU h225
    have hp1 : Log2CapPre w (dstMetaBase, (N, N)) s :=
      ⟨hdst_lt, hN_fit, hw_fit.of_le (by have := Nat.min_le_right N (Nat.log 2 N); omega)⟩)
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hp1
  all_goals (
    obtain ⟨_, _, _, hst1, hres1⟩ := log2CapProg_spec hp1.1 hp1.2.1 hp1.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 N)] at hres1
    repeat rw [hst1]
    repeat rw [clientState_maxNatProg]
    repeat rw [clientResult_maxNatProg]
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    have hp2 : Log2CapPre w (dstMetaBase, (max N 4 - 1, max N 4 - 1)) s :=
      ⟨hdst_lt, hmaxN4_fit.of_le (Nat.sub_le _ _),
        hw_fit.of_le (by have := Nat.min_le_right (max N 4 - 1) (Nat.log 2 (max N 4 - 1)); omega)⟩)
  all_goals try exact hp2
  all_goals (
    obtain ⟨_, _, _, hst2, hres2⟩ := log2CapProg_spec hp2.1 hp2.2.1 hp2.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres2
    repeat rw [hst2]
    repeat rw [hres2]
    repeat rw [hclog1_eq]
    have hp3 : Log2CapPre w (dstMetaBase, (Nat.clog 2 (max N 4) - 1, Nat.clog 2 (max N 4) - 1)) s :=
      ⟨hdst_lt, hw_fit.of_le (by omega),
        hw_fit.of_le (by
          have := Nat.min_le_right (Nat.clog 2 (max N 4) - 1)
            (Nat.log 2 (Nat.clog 2 (max N 4) - 1)); omega)⟩)
  all_goals try exact hp3
  all_goals (
    obtain ⟨_, _, _, _, hres3⟩ := log2CapProg_spec hp3.1 hp3.2.1 hp3.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres3
    repeat rw [hres3]
    repeat rw [hllf_eq]
    first
    | exact hw_fit.of_le (by omega)
    | exact h3llf.of_le (by omega))

/-- Read-only helper computing scales for `mkCompParams`. -/
private def computeCompScalesProg :
    (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | ((dstMetaBase, N), (logN, llf)) => do
    let threeLlf := llf * 3
    let bBits ← subSatProg (logN, threeLlf)
    let mBits ← minNatProg (logN, threeLlf)
    let numMicro := 1 <<< mBits
    let minCap ← minEffCapProg (N, numMicro)
    let logMinCap ← log2CapProg (dstMetaBase, (minCap, minCap))
    let lmBits := logMinCap + 1
    let sBits ← ifEqZeroProg (bBits, (0, llf + llf))
    let sSize := 1 <<< sBits
    let dirSlabs ← dirSlabsProg (bBits, llf)
    let tailCap ← ifEqZeroProg (bBits, (0, sSize + sSize))
    pure ((bBits, lmBits), ((numMicro, minCap), (sSize, (dirSlabs, tailCap))))

private def ComputeCompScalesPre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((dstMetaBase, N), (logN, llf)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      dstMetaBase < s.frontier ∧ Fits w 225

private theorem computeCompScales_arith {w U N : ℕ}
    (_hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (h225 : Fits w 225) :
    1 ≤ min N (effBucketCap N) ∧
    Nat.log 2 (min N (effBucketCap N)) + 1 = effBucketPosBits N ∧
    effBucketPosBits N ≤ w ∧
    (bucketBits N ≠ 0 → Fits w (2 ^ Dynamic.logLogFactor N * 4)) ∧
    Fits w (2 * slabSize N) := by
  have hN_fit : Fits w N := hU.of_le hNU
  have hminCap_pos : 1 ≤ min N (effBucketCap N) :=
    le_min hN (by
      unfold effBucketCap
      have : 0 < numMicroPerBucket N := by unfold numMicroPerBucket; positivity
      omega)
  have hlmBits_eq : Nat.log 2 (min N (effBucketCap N)) + 1 = effBucketPosBits N :=
    (clog2_succ_eq_log2_add_one hminCap_pos).symm
  have hlmBits_le : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hNU hU
  have hds : bucketBits N ≠ 0 → Fits w (2 ^ Dynamic.logLogFactor N * 4) := fun hb0 => by
    have hllf_lt : Dynamic.logLogFactor N + 2 ≤ Nat.log 2 N := by
      have := Dynamic.one_le_logLogFactor N; unfold bucketBits at hb0; omega
    have hpow_llf4 : 2 ^ Dynamic.logLogFactor N * 4 ≤ N := by
      calc 2 ^ Dynamic.logLogFactor N * 4
          = 2 ^ (Dynamic.logLogFactor N + 2) := by rw [pow_add]; ring
        _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos hllf_lt
        _ ≤ N := Nat.pow_log_le_self 2 (by omega)
    exact hN_fit.of_le hpow_llf4
  have h2s : Fits w (2 * slabSize N) := by
    by_cases hb0 : bucketBits N = 0
    · simp only [slabSize, slabBits, hb0, ↓reduceIte, pow_zero]
      exact h225.of_le (by decide)
    · have h2llf_lt : 2 * Dynamic.logLogFactor N + 1 ≤ Nat.log 2 N := by
        have := Dynamic.one_le_logLogFactor N; unfold bucketBits at hb0; omega
      have h2s_le : 2 * slabSize N ≤ N := by
        simp only [slabSize, slabBits, hb0, ↓reduceIte]
        calc 2 * 2 ^ (2 * Dynamic.logLogFactor N)
            = 2 ^ (2 * Dynamic.logLogFactor N + 1) := by rw [pow_succ']
          _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos h2llf_lt
          _ ≤ N := Nat.pow_log_le_self 2 (by omega)
      exact hN_fit.of_le h2s_le
  exact ⟨hminCap_pos, hlmBits_eq, hlmBits_le, hds, h2s⟩

private theorem computeCompScalesProg_exec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hdst_lt : dstMetaBase < s.frontier) (h225 : Fits w 225) :
    let d := ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeCompScalesProg d)) ∧
    (Memory.spec 0).clientState s (computeCompScalesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeCompScalesProg d) =
      ((bucketBits N, effBucketPosBits N),
        ((numMicroPerBucket N, min N (effBucketCap N)),
          (slabSize N, (dirSlabsPerBucket N, tailCapPerBucket N)))) ∧
    memoryCost (computeCompScalesProg d) s ≤ N := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hN_fit : Fits w N := hU.of_le hNU
  obtain ⟨_, hlmBits_eq, hlmBits_le, _, _⟩ := computeCompScales_arith hw hN hNU hU h225
  set minCap := min N (effBucketCap N)
  obtain ⟨_, hv_mc, hc_mc, hst_mc, hres_mc⟩ :=
    log2CapProg_spec (K := minCap) (x₀ := minCap) hdst_lt (hN_fit.of_le (min_le_left _ _))
      (hw_fit.of_le (by have := Nat.min_le_right minCap (Nat.log 2 minCap); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 minCap)] at hres_mc
  have h3llf_eq : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
  have hmBits_def : min (Nat.log 2 N) (3 * Dynamic.logLogFactor N) = microBits N := rfl
  have hnumMicro_eq : (1 <<< microBits N) = numMicroPerBucket N := by
    rw [Nat.shiftLeft_eq, one_mul]; rfl
  have hbBits_def : Nat.log 2 N - 3 * Dynamic.logLogFactor N = bucketBits N := rfl
  have hsBits_eq : (if bucketBits N = 0 then 0
      else Dynamic.logLogFactor N + Dynamic.logLogFactor N) = slabBits N := by
    dsimp only [slabBits]; rw [two_mul]
  have hsSize_eq : (1 <<< slabBits N) = slabSize N := by
    rw [Nat.shiftLeft_eq, one_mul]; rfl
  have htwoSSize_eq : slabSize N + slabSize N = 2 * slabSize N := by ring
  have hmin_le : minCap ≤ N := min_le_left _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, validHistory_bind', clientState_subSatProg, clientResult_subSatProg, hbBits_def]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_minNatProg, clientResult_minNatProg, hmBits_def]
    refine ⟨validHistory_minNatProg _ _, ?_⟩
    rw [hnumMicro_eq, validHistory_bind', clientState_minEffCapProg, clientResult_minEffCapProg]
    refine ⟨validHistory_minEffCapProg _ _, ?_⟩
    rw [validHistory_bind', hst_mc, hres_mc]; refine ⟨hv_mc, ?_⟩
    rw [hlmBits_eq, validHistory_bind', clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq]
    refine ⟨validHistory_ifEqZeroProg _ _, ?_⟩
    rw [hsSize_eq, htwoSSize_eq, validHistory_bind', clientState_dirSlabsProg,
      clientResult_dirSlabsProg]
    refine ⟨validHistory_dirSlabsProg _ _, ?_⟩
    rw [validHistory_bind', clientState_ifEqZeroProg]
    exact ⟨validHistory_ifEqZeroProg _ _, trivial⟩
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, StateTransitionSpec.clientState_bind, clientState_subSatProg,
      clientResult_subSatProg, hbBits_def,
      StateTransitionSpec.clientState_bind, clientState_minNatProg, clientResult_minNatProg,
      hmBits_def, hnumMicro_eq, StateTransitionSpec.clientState_bind, clientState_minEffCapProg,
      clientResult_minEffCapProg,
      StateTransitionSpec.clientState_bind, hst_mc, hres_mc,
      StateTransitionSpec.clientState_bind, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq,
      StateTransitionSpec.clientState_bind, clientState_dirSlabsProg,
      StateTransitionSpec.clientState_bind, clientState_ifEqZeroProg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      hbBits_def, prog_clientResult_bind, clientState_minNatProg, clientResult_minNatProg,
      hmBits_def, hnumMicro_eq, prog_clientResult_bind, clientState_minEffCapProg,
      clientResult_minEffCapProg, prog_clientResult_bind, hst_mc, hres_mc,
      hlmBits_eq, prog_clientResult_bind, clientState_ifEqZeroProg, clientResult_ifEqZeroProg,
      hsBits_eq, hsSize_eq, htwoSSize_eq, prog_clientResult_bind, clientState_dirSlabsProg,
      clientResult_dirSlabsProg, prog_clientResult_bind, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, prog_clientResult_pure]
    rfl
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg, hbBits_def,
      Realization.memoryCost_bind', memoryCost_minNatProg, clientState_minNatProg,
      clientResult_minNatProg, hmBits_def,
      hnumMicro_eq, Realization.memoryCost_bind', memoryCost_minEffCapProg,
      clientState_minEffCapProg, clientResult_minEffCapProg,
      Realization.memoryCost_bind', hst_mc, hres_mc,
      Realization.memoryCost_bind', memoryCost_ifEqZeroProg, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq,
      Realization.memoryCost_bind', memoryCost_dirSlabsProg, clientState_dirSlabsProg,
      Realization.memoryCost_bind', memoryCost_ifEqZeroProg, clientState_ifEqZeroProg,
      memoryCost_pure]
    dsimp only [minCap] at hc_mc hmin_le ⊢
    omega

private theorem realizesBounded_computeCompScales :
    RealizesBounded .exact computeCompScalesProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      ComputeCompScalesPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hmin := realizesBounded_minNat
  have hmec := realizesBounded_minEffCap
  have hifz := realizesBounded_ifEqZero
  have hds := realizesBounded_dirSlabs
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, N⟩, ⟨logN, llf⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, rfl, hdst_lt, h225⟩ := h
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hN_fit : Fits w N := hU.of_le hNU
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hlogN_lt, _, _, _, _, _, h3llf⟩ := computeLogScales_arith hN hNU hU h225
    obtain ⟨_, hlmBits_eq, hlmBits_le, hds_fit, h2s_fit⟩ :=
      computeCompScales_arith hw hN hNU hU h225
    have h3llf_eq : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
    have hbBits_def : Nat.log 2 N - 3 * Dynamic.logLogFactor N = bucketBits N := rfl
    have hmBits_def : min (Nat.log 2 N) (3 * Dynamic.logLogFactor N) = microBits N := rfl
    have hnumMicro_eq : (1 <<< microBits N) = numMicroPerBucket N := by
      rw [Nat.shiftLeft_eq, one_mul]; rfl
    repeat rw [h3llf_eq]
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    repeat rw [hbBits_def]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg]
    repeat rw [hmBits_def]
    repeat rw [hnumMicro_eq]
    repeat rw [clientState_minEffCapProg]
    repeat rw [clientResult_minEffCapProg]
    have hmc_pre : Log2CapPre w (dstMetaBase, (min N (effBucketCap N), min N (effBucketCap N))) s :=
      ⟨hdst_lt, hN_fit.of_le (min_le_left _ _),
        hw_fit.of_le (by
          have := Nat.min_le_right (min N (effBucketCap N)) (Nat.log 2 (min N (effBucketCap N)))
          omega)⟩)
  all_goals try exact ⟨h225.of_le (by decide), hN_fit⟩
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hmc_pre
  all_goals (
    obtain ⟨_, _, _, hst_mc, hres_mc⟩ := log2CapProg_spec hmc_pre.1 hmc_pre.2.1 hmc_pre.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres_mc
    repeat rw [hst_mc]
    repeat rw [hres_mc]
    have hsBits_eq : (if bucketBits N = 0 then 0
        else Dynamic.logLogFactor N + Dynamic.logLogFactor N) = slabBits N := by
      dsimp only [slabBits]; rw [two_mul]
    have hsSize_eq : (1 <<< slabBits N) = slabSize N := by rw [Nat.shiftLeft_eq, one_mul]; rfl
    repeat rw [hlmBits_eq]
    repeat rw [clientState_ifEqZeroProg]
    repeat rw [clientResult_ifEqZeroProg]
    repeat rw [hsBits_eq]
    repeat rw [hsSize_eq])
  all_goals try exact ⟨h225.of_le (by decide), hds_fit⟩
  all_goals (
    have hmBits_le : microBits N ≤ Nat.log 2 N := Nat.min_le_left _ _
    first
    | exact hw_fit.of_le (by omega)
    | exact h3llf.of_le (by omega)
    | (unfold numMicroPerBucket
       exact hmax_fit.of_le ((Nat.pow_le_pow_right two_pos hmBits_le).trans
         (by rw [← totalMicroBits_eq_log]; exact totalMicroBuckets_le N)))
    | exact h2s_fit.of_le (by omega))

/-- Pure helper computing `(maxTail, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))`. -/
private def computeGmBasesProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × Tup4)
  | (bBits, (dirSlabs, tailCap)) => do
    let numBkts := 1 <<< bBits
    let maxTail := numBkts * tailCap
    let gmDirBase := 4 + numBkts * 3
    let gmTailPtr := gmDirBase + numBkts * dirSlabs
    pure (maxTail, ((gmDirBase, gmTailPtr), (gmTailPtr + maxTail, gmTailPtr + maxTail * 2)))

private def ComputeGmBasesPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (bBits, (dirSlabs, tailCap)), _s =>
    ∃ U dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      bBits = bucketBits N ∧ dirSlabs = dirSlabsPerBucket N ∧ tailCap = tailCapPerBucket N ∧
      Fits w (dstMetaBase + offCompItems U w N)

private theorem computeGmBasesProg_spec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (_hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (bucketBits N, (dirSlabsPerBucket N, tailCapPerBucket N))
    Fits w (globalMetaLen N) ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeGmBasesProg d)) ∧
    (Memory.spec 0).clientState s (computeGmBasesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeGmBasesProg d) =
      (maxTailItems N,
        ((gmSlabDirBase N, gmTailPtrBase N), (gmTailOwnerBase N, gmSlabMetaBase N))) ∧
    memoryCost (computeGmBasesProg d) s = 0 := by
  intro d
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hgmLen_fit : Fits w (globalMetaLen N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · simp only [globalMetaLen, globalMetaVarLen, hb0, ↓reduceIte]
      exact h225.of_le (by decide)
    · exact fits_of_le_globalMetaLen_comp hb_pos hw hNU hU le_rfl
  refine ⟨hgmLen_fit, trivial, rfl, ?_, rfl⟩
  dsimp only [d, computeGmBasesProg]
  rw [prog_clientResult_pure, Nat.shiftLeft_eq, one_mul]
  change (numBuckets N * tailCapPerBucket N,
    ((4 + numBuckets N * 3, 4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N),
      (4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N +
        numBuckets N * tailCapPerBucket N,
       4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N +
        (numBuckets N * tailCapPerBucket N) * 2))) = _
  dsimp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase, maxTailItems]
  ext <;> dsimp only <;> ring

private theorem realizesBounded_computeGmBases :
    RealizesBounded .exact computeGmBasesProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × Tup4))
      ComputeGmBasesPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨bBits, ⟨dirSlabs, tailCap⟩⟩
    obtain ⟨U, dstMetaBase, N, hw, hN, hNU, hU, rfl, rfl, rfl, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hgmLen_fit, _, _, _, _⟩ := computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
    have hlogN_lt : Nat.log 2 N < w := (computeLogScales_arith hN hNU hU h225).1
    have hbBits_le : bucketBits N ≤ Nat.log 2 N := Nat.sub_le _ _
    try rw [Nat.shiftLeft_eq, one_mul]
    first
    | exact h225.of_le (by decide)
    | exact hmax_fit.of_le ((Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits N)).trans
        (totalMicroBuckets_le N))
    | (by_cases hb0 : bucketBits N = 0
       · simp only [tailCapPerBucket, dirSlabsPerBucket, hb0, ↓reduceIte, pow_zero]
         exact h225.of_le (by omega)
       · have hgm_pos : gmSlabMetaBase N + maxFullSlabs N * 4 = globalMetaLen N := by
           have := globalMetaLen_cond_eq N; simp only [hb0, ↓reduceIte] at this; exact this
         unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase maxTailItems
           numBuckets at hgm_pos
         exact hgmLen_fit.of_le (by omega)))

/-- Helper computing `(lmSubW, (gmWords, tailWords))` for `mkCompParams`. -/
private def computeMetaWordsProg : (Tup4 × Tup4) → Memory.Prog Tup3
  | (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta))) => do
    let maxSlabs ← maxSlabsProg (bBits, (N, sSize))
    let gmLen ← ifEqZeroProg (bBits, (4, gmSlabMeta + maxSlabs * 4))
    let lmSubW ← compPackedWordsProg ((1 <<< logN, lmBits), wVal)
    let gmWords ← compPackedWordsProg ((gmLen, logN + 1), wVal)
    let tailWords ← compPackedWordsProg ((maxTail, logN + 1), wVal)
    pure (lmSubW, (gmWords, tailWords))

private def ComputeMetaWordsPre (w : ℕ) : (Tup4 × Tup4) → Memory.State → Prop
  | (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta))), _s =>
    ∃ U dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ bBits = bucketBits N ∧ lmBits = effBucketPosBits N ∧
      logN = Nat.log 2 N ∧ sSize = slabSize N ∧ maxTail = maxTailItems N ∧
      gmSlabMeta = gmSlabMetaBase N ∧
      Fits w (dstMetaBase + offCompItems U w N)

private theorem computeMetaWordsProg_spec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (_hNU : N ≤ U) (_hU : Fits w U)
    (_hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((w, N), (bucketBits N, effBucketPosBits N)),
      ((Nat.log 2 N, slabSize N), (maxTailItems N, gmSlabMetaBase N)))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeMetaWordsProg d)) ∧
    (Memory.spec 0).clientState s (computeMetaWordsProg d) = s ∧
    (Memory.spec 0).clientResult s (computeMetaWordsProg d) =
      (lmSubWords N w,
        (packedWords (globalMetaLen N) (globalPtrBits N) w,
          packedWords (maxTailItems N) (globalPtrBits N) w)) ∧
    memoryCost (computeMetaWordsProg d) s = 0 := by
  intro d
  have hgmBits_eq : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
  have htotMicro_eq : (1 <<< Nat.log 2 N) = totalMicroBuckets N := by
    rw [Nat.shiftLeft_eq, one_mul, ← totalMicroBits_eq_log]; rfl
  have hgmLen_eq := globalMetaLen_cond_eq N
  have hv_pw : ∀ p st, (Memory.spec w).ValidHistory st
      ((Memory.spec w).clientHistory st (compPackedWordsProg p)) := by
    rintro ⟨⟨len, k⟩, wV⟩ st
    dsimp only [compPackedWordsProg]; simp only [pure_bind]; split_ifs <;> trivial
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeMetaWordsProg]
    rw [htotMicro_eq, hgmBits_eq, validHistory_bind', clientState_maxSlabsProg,
      clientResult_maxSlabsProg]
    refine ⟨validHistory_maxSlabsProg _ _, ?_⟩
    rw [validHistory_bind', clientState_ifEqZeroProg, clientResult_ifEqZeroProg, hgmLen_eq]
    refine ⟨validHistory_ifEqZeroProg _ _, ?_⟩
    rw [validHistory_bind', clientState_compPackedWordsProg]; refine ⟨hv_pw _ s, ?_⟩
    rw [validHistory_bind', clientState_compPackedWordsProg]; refine ⟨hv_pw _ s, ?_⟩
    rw [validHistory_bind', clientState_compPackedWordsProg]; exact ⟨hv_pw _ s, trivial⟩
  · dsimp only [d, computeMetaWordsProg]
    rw [StateTransitionSpec.clientState_bind, clientState_maxSlabsProg,
      StateTransitionSpec.clientState_bind, clientState_ifEqZeroProg,
      StateTransitionSpec.clientState_bind, clientState_compPackedWordsProg,
      StateTransitionSpec.clientState_bind, clientState_compPackedWordsProg,
      StateTransitionSpec.clientState_bind, clientState_compPackedWordsProg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeMetaWordsProg]
    rw [htotMicro_eq, hgmBits_eq,
      prog_clientResult_bind, clientState_maxSlabsProg, clientResult_maxSlabsProg,
      prog_clientResult_bind, clientState_ifEqZeroProg, clientResult_ifEqZeroProg, hgmLen_eq,
      prog_clientResult_bind, clientState_compPackedWordsProg, clientResult_compPackedWordsProg hw,
      prog_clientResult_bind, clientState_compPackedWordsProg, clientResult_compPackedWordsProg hw,
      prog_clientResult_bind, clientState_compPackedWordsProg, clientResult_compPackedWordsProg hw,
      prog_clientResult_pure]
    rfl
  · dsimp only [d, computeMetaWordsProg]
    rw [Realization.memoryCost_bind', memoryCost_maxSlabsProg, clientState_maxSlabsProg,
      Realization.memoryCost_bind', memoryCost_ifEqZeroProg, clientState_ifEqZeroProg,
      Realization.memoryCost_bind', memoryCost_compPackedWordsProg, clientState_compPackedWordsProg,
      Realization.memoryCost_bind', memoryCost_compPackedWordsProg, clientState_compPackedWordsProg,
      Realization.memoryCost_bind', memoryCost_compPackedWordsProg, clientState_compPackedWordsProg,
      memoryCost_pure]

private theorem realizesBounded_computeMetaWords :
    RealizesBounded .exact computeMetaWordsProg
      (WordEncoding.encode (α := Tup4 × Tup4))
      (WordEncoding.encode (α := Tup3))
      ComputeMetaWordsPre (fun _ _ => 0) := by
  have hms := realizesBounded_maxSlabs
  have hifz := realizesBounded_ifEqZero
  have hpw := realizesBounded_compPackedWords
  realize
  all_goals (
    rcases d with ⟨⟨⟨wVal, N⟩, ⟨bBits, lmBits⟩⟩, ⟨⟨logN, sSize⟩, ⟨maxTail, gmSlabMeta⟩⟩⟩
    obtain ⟨U, dstMetaBase, hw, hN, hNU, hU, hwVal, rfl, rfl, rfl, rfl, rfl, rfl, hfit_dst⟩ := h
    subst wVal
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hgmLen_fit, _, _, _, _⟩ := computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
    obtain ⟨hlogN_lt, _, _, _, _, _, _⟩ := computeLogScales_arith hN hNU hU h225
    have hgmBits_eq : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
    have htotMicro_eq : (1 <<< Nat.log 2 N) = totalMicroBuckets N := by
      rw [Nat.shiftLeft_eq, one_mul, ← totalMicroBits_eq_log]; rfl
    repeat rw [hgmBits_eq]
    repeat rw [htotMicro_eq]
    repeat rw [clientState_maxSlabsProg]
    repeat rw [clientResult_maxSlabsProg]
    repeat rw [clientState_ifEqZeroProg]
    repeat rw [clientResult_ifEqZeroProg]
    repeat rw [globalMetaLen_cond_eq]
    repeat rw [clientState_compPackedWordsProg])
  all_goals try (intro _; unfold slabSize; positivity)
  all_goals try (
    dsimp only [CompPackedWordsPre]
    refine ⟨hw, rfl, ?_, ?_, ?_, h225.of_le (u := 3) (by decide)⟩
    · first
      | exact effBucketPosBits_le_of_lt_pow hNU hU
      | exact globalPtrBits_le_of_lt_pow hNU hU
    · first
      | exact hmax_fit.of_le (totalMicroBuckets_le N)
      | exact hgmLen_fit
      | exact hU.of_le ((maxTailItems_le N).trans hNU)
    · refine hfit_dst.of_le ?_
      (try change lmSubWords N w ≤ _)
      unfold offCompItems offDenseToTail offTailToDense offCompGM; omega)
  all_goals (
    have hgmBits_le : globalPtrBits N ≤ w := globalPtrBits_le_of_lt_pow hNU hU
    first
    | (refine h225.of_le ?_; decide)
    | (refine hw_fit.of_le ?_; omega)
    | exact hmax_fit.of_le (totalMicroBuckets_le N)
    | (by_cases hb0 : bucketBits N = 0
       · simp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase, maxTailItems,
           tailCapPerBucket, dirSlabsPerBucket, maxFullSlabs, numBuckets, hb0, ↓reduceIte,
           pow_zero, mul_zero, add_zero]
         refine h225.of_le ?_; decide
       · have hgm_pos : gmSlabMetaBase N + maxFullSlabs N * 4 = globalMetaLen N := by
           have := globalMetaLen_cond_eq N; simp only [hb0, ↓reduceIte] at this; exact this
         refine hgmLen_fit.of_le ?_; omega))

/-- Write indices `0..7` of `mkCompParams` at `[cpBase, +8)` and return `offCompLMSub U w N 3`. -/
private def writeCompSubAProg : Tup4 × Tup3 → Memory.Prog ℕ
  | (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW))) => do
    let off0 := 225 + hSpace
    writeBlock4Prog (cpBase, ((wVal, N), (N - 1, qBitsVal)))
    writeBlock4Prog (cpBase + 4, ((vBits, off0), (off0 + lmSubW, off0 + lmSubW * 2)))
    pure (off0 + lmSubW * 3)

private def WriteCompSubAPre (w : ℕ) : Tup4 × Tup3 → Memory.State → Prop
  | (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW))), s =>
    ∃ U V dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      hSpace = epochHashSpace U w N ∧ lmSubW = lmSubWords N w ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubAProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, w), (N, quotientBits U N)),
      (valBits V, (epochHashSpace U w N, lmSubWords N w)))
    let prog := writeCompSubAProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubAPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompLMSub U w N 3 ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 27 + j) = mkCompParams U V w N ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 27 ≤ a ∧ a < dstMetaBase + 35) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  set cp := mkCompParams U V w N
  have ho0 : 225 + epochHashSpace U w N = offCompLMSub U w N 0 := by
    dsimp only [offCompLMSub, offCompLM, epochHdrWords]; ring
  have ho1 : 225 + epochHashSpace U w N + lmSubWords N w = offCompLMSub U w N 1 := by
    dsimp only [offCompLMSub, offCompLM, epochHdrWords]; ring
  have ho2 : 225 + epochHashSpace U w N + lmSubWords N w * 2 = offCompLMSub U w N 2 := by
    dsimp only [offCompLMSub, offCompLM, epochHdrWords]; ring
  have ho3 : 225 + epochHashSpace U w N + lmSubWords N w * 3 = offCompLMSub U w N 3 := by
    dsimp only [offCompLMSub, offCompLM, epochHdrWords]; ring
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27) (cp 0) (cp 1) (cp 2) (cp 3) (s := s)
      (by omega) (hfit63.of_le (by omega)) (hcp 0) (hcp 1) (hcp 2) (hcp 3)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 27, ((cp 0, cp 1), (cp 2, cp 3))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 4) (cp 4) (cp 5) (cp 6) (cp 7) (s := s1)
      (by omega) (hfit63.of_le (by omega)) (hcp 4) (hcp 5) (hcp 6) (hcp 7)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock4Prog (dstMetaBase + 27 + 4, ((cp 4, cp 5), (cp 6, cp 7))))
  have hb1_eq : writeBlock4Prog (dstMetaBase + 27 + 4,
      ((valBits V, 225 + epochHashSpace U w N),
       (225 + epochHashSpace U w N + lmSubWords N w,
        225 + epochHashSpace U w N + lmSubWords N w * 2))) =
      writeBlock4Prog (dstMetaBase + 27 + 4, ((cp 4, cp 5), (cp 6, cp 7))) := by
    rw [ho2, ho1, ho0]; rfl
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeCompSubAProg]
    rw [hb1_eq]; rfl
  refine ⟨⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompSubAProg]
    rw [hb1_eq, validHistory_bind']; refine ⟨hv0, ?_⟩
    rw [validHistory_bind']; exact ⟨hv1, trivial⟩
  · dsimp only [prog, d, writeCompSubAProg]
    rw [hb1_eq, prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure]
    exact ho3
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Nat.add_zero, hframe1 _ (by omega)]; exact m00
    · rw [hframe1 _ (by omega)]; exact m01
    · rw [hframe1 _ (by omega)]; exact m02
    · rw [hframe1 _ (by omega)]; exact m03
    · exact m10
    · rw [show dstMetaBase + 27 + 5 = dstMetaBase + 27 + 4 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 27 + 6 = dstMetaBase + 27 + 4 + 2 by omega]; exact m12
    · rw [show dstMetaBase + 27 + 7 = dstMetaBase + 27 + 4 + 3 by omega]; exact m13
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeCompSubAProg]
    rw [hb1_eq]
    change memoryCost
      (writeBlock4Prog (dstMetaBase + 27, ((cp 0, cp 1), (cp 2, cp 3))) >>= fun _ =>
        writeBlock4Prog (dstMetaBase + 27 + 4, ((cp 4, cp 5), (cp 6, cp 7))) >>= fun _ =>
          pure (225 + epochHashSpace U w N + lmSubWords N w * 3)) s = 8
    rw [Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeBlock4Prog (dstMetaBase + 27, ((cp 0, cp 1), (cp 2, cp 3)))) s +
      (memoryCost (writeBlock4Prog (dstMetaBase + 27 + 4, ((cp 4, cp 5), (cp 6, cp 7)))) s1 + 0) = 8
    rw [hc0, hc1]

private theorem realizesBounded_writeCompSubA :
    RealizesBounded .exact writeCompSubAProg
      (WordEncoding.encode (α := Tup4 × Tup3)) (WordEncoding.encode (α := ℕ))
      WriteCompSubAPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, wVal⟩, ⟨N, qBitsVal⟩⟩, ⟨vBits, ⟨hSpace, lmSubW⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, hw, hN, hNU, hU, _hV, rfl, hwVal, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    subst wVal
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hN_fit : Fits w N := hU.of_le hNU
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals try exact hN
  all_goals (
    first
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
       omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Write indices `8..15` of `mkCompParams` at `[cpBase + 8, +8)` and return `offCompGM U w N`. -/
private def writeCompSubBProg : Tup4 → Memory.Prog ℕ
  | ((cpBase, off3), (lmSubW, lmBits)) => do
    writeBlock4Prog (cpBase + 8,
      ((off3, off3 + lmSubW), (off3 + lmSubW * 2, off3 + lmSubW * 3)))
    writeBlock4Prog (cpBase + 12,
      ((off3 + lmSubW * 4, off3 + lmSubW * 5), (lmBits, off3 + lmSubW * 6)))
    pure (off3 + lmSubW * 6)

private def WriteCompSubBPre (w : ℕ) : Tup4 → Memory.State → Prop
  | ((cpBase, off3), (lmSubW, lmBits)), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ off3 = offCompLMSub U w N 3 ∧
      lmSubW = lmSubWords N w ∧ lmBits = effBucketPosBits N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubBProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase + 27, offCompLMSub U w N 3), (lmSubWords N w, effBucketPosBits N))
    let prog := writeCompSubBProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubBPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompGM U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 35 + j) = mkCompParams U V w N ⟨8 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 35 ≤ a ∧ a < dstMetaBase + 43) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  set cp := mkCompParams U V w N
  have ho4 : offCompLMSub U w N 3 + lmSubWords N w = offCompLMSub U w N 4 := by
    dsimp only [offCompLMSub]; ring
  have ho5 : offCompLMSub U w N 3 + lmSubWords N w * 2 = offCompLMSub U w N 5 := by
    dsimp only [offCompLMSub]; ring
  have ho6 : offCompLMSub U w N 3 + lmSubWords N w * 3 = offCompLMSub U w N 6 := by
    dsimp only [offCompLMSub]; ring
  have ho7 : offCompLMSub U w N 3 + lmSubWords N w * 4 = offCompLMSub U w N 7 := by
    dsimp only [offCompLMSub]; ring
  have ho8 : offCompLMSub U w N 3 + lmSubWords N w * 5 = offCompLMSub U w N 8 := by
    dsimp only [offCompLMSub]; ring
  have hogm : offCompLMSub U w N 3 + lmSubWords N w * 6 = offCompGM U w N := by
    dsimp only [offCompGM, offCompLMSub]; ring
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 8) (cp 8) (cp 9) (cp 10) (cp 11) (s := s)
      (by omega) (hfit63.of_le (by omega)) (hcp 8) (hcp 9) (hcp 10) (hcp 11)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 27 + 8, ((cp 8, cp 9), (cp 10, cp 11))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 12) (cp 12) (cp 13) (cp 14) (cp 15) (s := s1)
      (by omega) (hfit63.of_le (by omega)) (hcp 12) (hcp 13) (hcp 14) (hcp 15)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock4Prog (dstMetaBase + 27 + 12, ((cp 12, cp 13), (cp 14, cp 15))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 27 + 8,
      ((offCompLMSub U w N 3, offCompLMSub U w N 3 + lmSubWords N w),
       (offCompLMSub U w N 3 + lmSubWords N w * 2,
        offCompLMSub U w N 3 + lmSubWords N w * 3))) =
      writeBlock4Prog (dstMetaBase + 27 + 8, ((cp 8, cp 9), (cp 10, cp 11))) := by
    rw [ho6, ho5, ho4]; rfl
  have hb1_eq : writeBlock4Prog (dstMetaBase + 27 + 12,
      ((offCompLMSub U w N 3 + lmSubWords N w * 4,
        offCompLMSub U w N 3 + lmSubWords N w * 5),
       (effBucketPosBits N, offCompLMSub U w N 3 + lmSubWords N w * 6))) =
      writeBlock4Prog (dstMetaBase + 27 + 12, ((cp 12, cp 13), (cp 14, cp 15))) := by
    rw [hogm, ho8, ho7]; rfl
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeCompSubBProg]
    rw [hb0_eq, hb1_eq]; rfl
  refine ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, h63, hfit_dst⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompSubBProg]
    rw [hb0_eq, hb1_eq, validHistory_bind']; refine ⟨hv0, ?_⟩
    rw [validHistory_bind']; exact ⟨hv1, trivial⟩
  · dsimp only [prog, d, writeCompSubBProg]
    rw [hb0_eq, hb1_eq, prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure]
    exact hogm
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 35 + 0 = dstMetaBase + 27 + 8 by omega, hframe1 _ (by omega)]
      exact m00
    · rw [show dstMetaBase + 35 + 1 = dstMetaBase + 27 + 8 + 1 by omega, hframe1 _ (by omega)]
      exact m01
    · rw [show dstMetaBase + 35 + 2 = dstMetaBase + 27 + 8 + 2 by omega, hframe1 _ (by omega)]
      exact m02
    · rw [show dstMetaBase + 35 + 3 = dstMetaBase + 27 + 8 + 3 by omega, hframe1 _ (by omega)]
      exact m03
    · rw [show dstMetaBase + 35 + 4 = dstMetaBase + 27 + 12 by omega]; exact m10
    · rw [show dstMetaBase + 35 + 5 = dstMetaBase + 27 + 12 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 35 + 6 = dstMetaBase + 27 + 12 + 2 by omega]; exact m12
    · rw [show dstMetaBase + 35 + 7 = dstMetaBase + 27 + 12 + 3 by omega]; exact m13
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeCompSubBProg]
    rw [hb0_eq, hb1_eq, Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeBlock4Prog _) s + (memoryCost (writeBlock4Prog _) s1 + 0) = 8
    rw [hc0, hc1]

private theorem realizesBounded_writeCompSubB :
    RealizesBounded .exact writeCompSubBProg
      (WordEncoding.encode (α := Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompSubBPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨cpBase, off3⟩, ⟨lmSubW, lmBits⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, h63, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals (
    first
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub
       omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Write indices `16..23` of `mkCompParams` at `[cpBase + 16, +8)` and return
`offCompItems U w N`. -/
private def writeCompSubCProg : Tup4 × Tup4 → Memory.Prog ℕ
  | (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize))) => do
    let offTD := offGM + gmWords
    let offDT := offTD + tailWords
    writeBlock4Prog (cpBase + 16, ((logN + 1, offTD), (offDT, maxTail)))
    writeBlock4Prog (cpBase + 20, ((bBits, (1 <<< bBits) - 1), (sSize, sSize - 1)))
    pure (offDT + tailWords)

private def WriteCompSubCPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize))), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ offGM = offCompGM U w N ∧
      gmWords = packedWords (globalMetaLen N) (globalPtrBits N) w ∧
      tailWords = packedWords (maxTailItems N) (globalPtrBits N) w ∧
      logN = Nat.log 2 N ∧ maxTail = maxTailItems N ∧
      bBits = bucketBits N ∧ sSize = slabSize N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubCProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, offCompGM U w N),
      (packedWords (globalMetaLen N) (globalPtrBits N) w,
       packedWords (maxTailItems N) (globalPtrBits N) w)),
      ((Nat.log 2 N, maxTailItems N), (bucketBits N, slabSize N)))
    let prog := writeCompSubCProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubCPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompItems U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 43 + j) = mkCompParams U V w N ⟨16 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 43 ≤ a ∧ a < dstMetaBase + 51) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  set cp := mkCompParams U V w N
  have h16 : Nat.log 2 N + 1 = globalPtrBits N := (clog2_succ_eq_log2_add_one hN).symm
  have h21 : (1 <<< bucketBits N) - 1 = 2 ^ bucketBits N - 1 := by
    rw [Nat.shiftLeft_eq, one_mul]
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 16) (cp 16) (cp 17) (cp 18) (cp 19) (s := s)
      (by omega) (hfit63.of_le (by omega)) (hcp 16) (hcp 17) (hcp 18) (hcp 19)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 27 + 16, ((cp 16, cp 17), (cp 18, cp 19))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 20) (cp 20) (cp 21) (cp 22) (cp 23) (s := s1)
      (by omega) (hfit63.of_le (by omega)) (hcp 20) (hcp 21) (hcp 22) (hcp 23)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock4Prog (dstMetaBase + 27 + 20, ((cp 20, cp 21), (cp 22, cp 23))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 27 + 16,
      ((Nat.log 2 N + 1, offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w),
       (offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w +
         packedWords (maxTailItems N) (globalPtrBits N) w, maxTailItems N))) =
      writeBlock4Prog (dstMetaBase + 27 + 16, ((cp 16, cp 17), (cp 18, cp 19))) := by
    rw [h16]; rfl
  have hb1_eq : writeBlock4Prog (dstMetaBase + 27 + 20,
      ((bucketBits N, (1 <<< bucketBits N) - 1), (slabSize N, slabSize N - 1))) =
      writeBlock4Prog (dstMetaBase + 27 + 20, ((cp 20, cp 21), (cp 22, cp 23))) := by
    rw [h21]; rfl
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeCompSubCProg]
    rw [hb0_eq, hb1_eq]; rfl
  refine ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompSubCProg]
    rw [hb0_eq, hb1_eq, validHistory_bind']; refine ⟨hv0, ?_⟩
    rw [validHistory_bind']; exact ⟨hv1, trivial⟩
  · dsimp only [prog, d, writeCompSubCProg]
    rw [hb0_eq, hb1_eq, prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure]
    rfl
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 43 + 0 = dstMetaBase + 27 + 16 by omega, hframe1 _ (by omega)]
      exact m00
    · rw [show dstMetaBase + 43 + 1 = dstMetaBase + 27 + 16 + 1 by omega, hframe1 _ (by omega)]
      exact m01
    · rw [show dstMetaBase + 43 + 2 = dstMetaBase + 27 + 16 + 2 by omega, hframe1 _ (by omega)]
      exact m02
    · rw [show dstMetaBase + 43 + 3 = dstMetaBase + 27 + 16 + 3 by omega, hframe1 _ (by omega)]
      exact m03
    · rw [show dstMetaBase + 43 + 4 = dstMetaBase + 27 + 20 by omega]; exact m10
    · rw [show dstMetaBase + 43 + 5 = dstMetaBase + 27 + 20 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 43 + 6 = dstMetaBase + 27 + 20 + 2 by omega]; exact m12
    · rw [show dstMetaBase + 43 + 7 = dstMetaBase + 27 + 20 + 3 by omega]; exact m13
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeCompSubCProg]
    rw [hb0_eq, hb1_eq, Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeBlock4Prog _) s + (memoryCost (writeBlock4Prog _) s1 + 0) = 8
    rw [hc0, hc1]

private theorem realizesBounded_writeCompSubC :
    RealizesBounded .exact writeCompSubCProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompSubCPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, offGM⟩, ⟨gmWords, tailWords⟩⟩, ⟨⟨logN, maxTail⟩, ⟨bBits, sSize⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    have hlogN_lt : Nat.log 2 N < w := (computeLogScales_arith hN hNU hU h225).1
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact hfit63.of_le (by omega)
  all_goals try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow)
  all_goals (
    first
    | exact (by unfold slabSize; exact Nat.one_le_two_pow : 1 ≤ slabSize N)
    | exact hw_fit.of_le (by omega)
    | (rw [Nat.shiftLeft_eq, one_mul]
       have h2b : 2 ^ bucketBits N ≤ max N 1 :=
         (Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits N)).trans
           (totalMicroBuckets_le N)
       exact hmax_fit.of_le (by omega))
    | (refine hfit_dst.of_le ?_
       unfold offCompItems offDenseToTail offTailToDense offCompGM; omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Write indices `24..31` of `mkCompParams` at `[cpBase + 24, +8)`. -/
private def writeCompSubDProg : Tup4 × Tup4 → Memory.Prog Unit
  | (((cpBase, sSize), (dirSlabs, tailCap)), ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))) =>
    do
      let dirSlabsSub1 ← subSatProg (dirSlabs, 1)
      writeBlock4Prog (cpBase + 24, ((sSize + sSize, dirSlabs), (dirSlabsSub1, tailCap)))
      writeBlock4Prog (cpBase + 28, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))

private def WriteCompSubDPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, sSize), (dirSlabs, tailCap)),
      ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))), s =>
    ∃ U V dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ sSize = slabSize N ∧ dirSlabs = dirSlabsPerBucket N ∧
      tailCap = tailCapPerBucket N ∧ gmDirBase = gmSlabDirBase N ∧
      gmTailPtr = gmTailPtrBase N ∧ gmTailOwn = gmTailOwnerBase N ∧
      gmSlabMeta = gmSlabMetaBase N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubDProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, slabSize N), (dirSlabsPerBucket N, tailCapPerBucket N)),
      ((gmSlabDirBase N, gmTailPtrBase N), (gmTailOwnerBase N, gmSlabMetaBase N)))
    let prog := writeCompSubDProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubDPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 51 + j) = mkCompParams U V w N ⟨24 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 51 ≤ a ∧ a < dstMetaBase + 59) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 8 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  set cp := mkCompParams U V w N
  have h24 : slabSize N + slabSize N = 2 * slabSize N := by ring
  obtain ⟨_, hv0, hfr0, hm0, hframe0, hc0⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 24) (cp 24) (cp 25) (cp 26) (cp 27) (s := s)
      (by omega) (hfit63.of_le (by omega)) (hcp 24) (hcp 25) (hcp 26) (hcp 27)
  set s1 := (Memory.spec 0).clientState s
    (writeBlock4Prog (dstMetaBase + 27 + 24, ((cp 24, cp 25), (cp 26, cp 27))))
  obtain ⟨_, hv1, hfr1, hm1, hframe1, hc1⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 28) (cp 28) (cp 29) (cp 30) (cp 31) (s := s1)
      (by omega) (hfit63.of_le (by omega)) (hcp 28) (hcp 29) (hcp 30) (hcp 31)
  set s2 := (Memory.spec 0).clientState s1
    (writeBlock4Prog (dstMetaBase + 27 + 28, ((cp 28, cp 29), (cp 30, cp 31))))
  have hb0_eq : writeBlock4Prog (dstMetaBase + 27 + 24,
      ((slabSize N + slabSize N, dirSlabsPerBucket N),
       (dirSlabsPerBucket N - 1, tailCapPerBucket N))) =
      writeBlock4Prog (dstMetaBase + 27 + 24, ((cp 24, cp 25), (cp 26, cp 27))) := by
    rw [h24]; rfl
  have hs'_eq : s' = s2 := by
    dsimp only [s', prog, d, writeCompSubDProg]
    rw [StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      hb0_eq, StateTransitionSpec.clientState_bind]
    rfl
  refine ⟨⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompSubDProg]
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [hb0_eq, validHistory_bind']; exact ⟨hv0, hv1⟩
  · rw [hs'_eq, hfr1, hfr0]
  · intro j hj
    rw [hs'_eq]
    obtain ⟨m00, m01, m02, m03⟩ := hm0
    obtain ⟨m10, m11, m12, m13⟩ := hm1
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 51 + 0 = dstMetaBase + 27 + 24 by omega, hframe1 _ (by omega)]
      exact m00
    · rw [show dstMetaBase + 51 + 1 = dstMetaBase + 27 + 24 + 1 by omega, hframe1 _ (by omega)]
      exact m01
    · rw [show dstMetaBase + 51 + 2 = dstMetaBase + 27 + 24 + 2 by omega, hframe1 _ (by omega)]
      exact m02
    · rw [show dstMetaBase + 51 + 3 = dstMetaBase + 27 + 24 + 3 by omega, hframe1 _ (by omega)]
      exact m03
    · rw [show dstMetaBase + 51 + 4 = dstMetaBase + 27 + 28 by omega]; exact m10
    · rw [show dstMetaBase + 51 + 5 = dstMetaBase + 27 + 28 + 1 by omega]; exact m11
    · rw [show dstMetaBase + 51 + 6 = dstMetaBase + 27 + 28 + 2 by omega]; exact m12
    · rw [show dstMetaBase + 51 + 7 = dstMetaBase + 27 + 28 + 3 by omega]; exact m13
  · intro a ha
    rw [hs'_eq, hframe1 a (by omega), hframe0 a (by omega)]
  · dsimp only [prog, d, writeCompSubDProg]
    rw [Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg, hb0_eq, Realization.memoryCost_bind']
    change 0 +
      (memoryCost (writeBlock4Prog (dstMetaBase + 27 + 24, ((cp 24, cp 25), (cp 26, cp 27)))) s +
        memoryCost (writeBlock4Prog (dstMetaBase + 27 + 28, ((cp 28, cp 29), (cp 30, cp 31)))) s1) =
      8
    rw [hc0, hc1]

private theorem realizesBounded_writeCompSubD :
    RealizesBounded .exact writeCompSubDProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := Unit))
      WriteCompSubDPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨⟨⟨cpBase, sSize⟩, ⟨dirSlabs, tailCap⟩⟩,
      ⟨⟨gmDirBase, gmTailPtr⟩, ⟨gmTailOwn, gmSlabMeta⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, _hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
    obtain ⟨_, _, _, _, h2s_fit⟩ := computeCompScales_arith hw hN hNU hU h225
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg])
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hfit63.of_le (by omega)
  all_goals (
    first
    | exact h2s_fit.of_le (by omega)
    | (refine ⟨?_, hfit63.of_le (by omega)⟩
       try dsimp only [StateTransitionSpec.clientState, writeBlock4Prog]
       try simp only [prog_runClient_state_bind, prog_runClient_state_write]
       omega))

/-- Write indices `32..35` of `mkCompParams` at `[cpBase + 32, +4)`. -/
private def writeCompSubEProg : ℕ × Tup4 → Memory.Prog Unit
  | (cpBase, ((numMicro, minCap), (offItemsVal, hSpace))) =>
    writeBlock4Prog (cpBase + 32, ((numMicro, minCap), (offItemsVal, hSpace)))

private def WriteCompSubEPre (w : ℕ) : ℕ × Tup4 → Memory.State → Prop
  | (cpBase, _), s =>
    ∃ U dstMetaBase N,
      cpBase = dstMetaBase + 27 ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompSubEProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (dstMetaBase + 27,
      ((numMicroPerBucket N, min N (effBucketCap N)),
       (offCompItems U w N, epochHashSpace U w N)))
    let prog := writeCompSubEProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompSubEPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 4),
      s'.mem (dstMetaBase + 59 + j) = mkCompParams U V w N ⟨32 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 59 ≤ a ∧ a < dstMetaBase + 63) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 4 := by
  intro d prog s'
  have hcp := fits_mkCompParams (V := V) hw hNU hU hV hfit_dst
  have hfit63 : Fits w (dstMetaBase + 63) :=
    hfit_dst.of_le (by
      unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
  obtain ⟨_, hv, hfr, hm, hframe, hc⟩ :=
    writeBlock4Prog_spec (dstMetaBase + 27 + 32)
      (numMicroPerBucket N) (min N (effBucketCap N)) (offCompItems U w N) (epochHashSpace U w N)
      (s := s) (by omega) (hfit63.of_le (by omega))
      (hcp 32) (hcp 33) (hcp 34) (hcp 35)
  refine ⟨⟨U, dstMetaBase, N, rfl, h63, hfit_dst⟩, hv, hfr, ?_, ?_, hc⟩
  · intro j hj
    obtain ⟨m0, m1, m2, m3⟩ := hm
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show dstMetaBase + 59 + 0 = dstMetaBase + 27 + 32 by omega]; exact m0
    · rw [show dstMetaBase + 59 + 1 = dstMetaBase + 27 + 32 + 1 by omega]; exact m1
    · rw [show dstMetaBase + 59 + 2 = dstMetaBase + 27 + 32 + 2 by omega]; exact m2
    · rw [show dstMetaBase + 59 + 3 = dstMetaBase + 27 + 32 + 3 by omega]; exact m3
  · intro a ha
    exact hframe a (by omega)

private theorem realizesBounded_writeCompSubE :
    RealizesBounded .exact writeCompSubEProg
      (WordEncoding.encode (α := ℕ × Tup4)) (WordEncoding.encode (α := Unit))
      WriteCompSubEPre (fun _ _ => 0) := by
  have hb4 := realizesBounded_writeBlock4
  realize
  all_goals (
    rcases d with ⟨cpBase, ⟨⟨numMicro, minCap⟩, ⟨offItemsVal, hSpace⟩⟩⟩
    obtain ⟨U, dstMetaBase, N, rfl, h63, hfit_dst⟩ := h
    dsimp only at *
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals first | exact hfit63.of_le (by omega) | exact ⟨by omega, hfit63.of_le (by omega)⟩

/-- Compute scales + GM bases and write indices `24..31` of `mkCompParams` at
`[dstMetaBase + 51, +8)`. -/
private def writeCompScalesGmDProg :
    Tup4 → Memory.Prog ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | ((dstMetaBase, N), (logN, llf)) => do
    let ((bBits, lmBits), ((numMicro, minCap), (sSize, (dirSlabs, tailCap)))) ←
      computeCompScalesProg ((dstMetaBase, N), (logN, llf))
    let (maxTail, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta))) ←
      computeGmBasesProg (bBits, (dirSlabs, tailCap))
    writeCompSubDProg
      (((dstMetaBase + 27, sSize), (dirSlabs, tailCap)),
       ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))
    pure ((bBits, lmBits), ((numMicro, minCap), (sSize, (maxTail, gmSlabMeta))))

private def WriteCompScalesGmDPre (w : ℕ) : Tup4 → Memory.State → Prop
  | ((dstMetaBase, N), (logN, llf)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompScalesGmDProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N))
    let prog := writeCompScalesGmDProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompScalesGmDPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog =
      ((bucketBits N, effBucketPosBits N),
        ((numMicroPerBucket N, min N (effBucketCap N)),
          (slabSize N, (maxTailItems N, gmSlabMetaBase N)))) ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 8),
      s'.mem (dstMetaBase + 51 + j) = mkCompParams U V w N ⟨24 + j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 51 ≤ a ∧ a < dstMetaBase + 59) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ N + 12 := by
  intro d prog s'
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hdst_lt : dstMetaBase < s.frontier := by omega
  obtain ⟨hv_sc, hst_sc, hres_sc, hc_sc⟩ :=
    computeCompScalesProg_exec (s := s) hw hN hNU hU hdst_lt h225
  obtain ⟨_, hv_gm, hst_gm, hres_gm, hc_gm⟩ :=
    computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
  obtain ⟨_, hvD, hfrD, hmD, hframeD, hcD⟩ :=
    writeCompSubDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
  set sD := (Memory.spec 0).clientState s (writeCompSubDProg
    (((dstMetaBase + 27, slabSize N), (dirSlabsPerBucket N, tailCapPerBucket N)),
     ((gmSlabDirBase N, gmTailPtrBase N), (gmTailOwnerBase N, gmSlabMetaBase N))))
  have hs'_eq : s' = sD := by
    dsimp only [s', prog, d, writeCompScalesGmDProg]
    rw [StateTransitionSpec.clientState_bind, hst_sc, hres_sc]; dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_gm, hres_gm]; dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompScalesGmDProg]
    rw [validHistory_bind', hst_sc, hres_sc]; refine ⟨hv_sc, ?_⟩
    dsimp only; rw [validHistory_bind', hst_gm, hres_gm]; refine ⟨hv_gm, ?_⟩
    dsimp only; rw [validHistory_bind']; exact ⟨hvD, trivial⟩
  · dsimp only [prog, d, writeCompScalesGmDProg]
    rw [prog_clientResult_bind, hst_sc, hres_sc]; dsimp only
    rw [prog_clientResult_bind, hst_gm, hres_gm]; dsimp only
    rw [prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs'_eq, hfrD]
  · intro j hj; rw [hs'_eq]; exact hmD j hj
  · intro a ha; rw [hs'_eq]; exact hframeD a ha
  · dsimp only [prog, d, writeCompScalesGmDProg]
    rw [Realization.memoryCost_bind', hst_sc, hres_sc]; dsimp only
    rw [Realization.memoryCost_bind', hst_gm, hres_gm]; dsimp only
    rw [Realization.memoryCost_bind', memoryCost_pure]
    omega

private theorem realizesBounded_writeCompScalesGmD :
    RealizesBounded .exact writeCompScalesGmDProg
      (WordEncoding.encode (α := Tup4))
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      WriteCompScalesGmDPre (fun _ _ => 0) := by
  have hsc := realizesBounded_computeCompScales
  have hgm := realizesBounded_computeGmBases
  have hD := realizesBounded_writeCompSubD
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, N⟩, ⟨logN, llf⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩ := h
    dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hdst_lt : dstMetaBase < s.frontier := by omega
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega)
    obtain ⟨_, hst_sc, hres_sc, _⟩ :=
      computeCompScalesProg_exec (s := s) hw hN hNU hU hdst_lt h225
    obtain ⟨_, _, hst_gm, hres_gm, _⟩ :=
      computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst)
  all_goals try (refine hfit63.of_le ?_; omega)
  · exact ⟨U, hw, hN, hNU, hU, rfl, rfl, hdst_lt, h225⟩
  · rw [hst_sc, hres_sc]; dsimp only
    exact ⟨U, dstMetaBase, N, hw, hN, hNU, hU, rfl, rfl, rfl, hfit_dst⟩
  · rw [hst_sc, hres_sc]; dsimp only
    rw [hst_gm, hres_gm]; dsimp only
    exact ⟨U, 1, dstMetaBase, N, hw, hN, hNU, hU, Nat.one_le_two_pow,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩

/-- Write indices `0..15` of `mkCompParams` at `[cpBase, +16)` and return `offCompGM U w N`. -/
private def writeCompABProg : Tup4 × Tup4 → Memory.Prog ℕ
  | (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits))) => do
    let off3 ← writeCompSubAProg (((cpBase, wVal), (N, qBitsVal)), (vBits, (hSpace, lmSubW)))
    writeCompSubBProg ((cpBase, off3), (lmSubW, lmBits))

private def WriteCompABPre (w : ℕ) : Tup4 × Tup4 → Memory.State → Prop
  | (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits))), s =>
    ∃ U V dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      cpBase = dstMetaBase + 27 ∧ wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      hSpace = epochHashSpace U w N ∧ lmSubW = lmSubWords N w ∧ lmBits = effBucketPosBits N ∧
      dstMetaBase + 63 ≤ s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompABProg_spec {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (((dstMetaBase + 27, w), (N, quotientBits U N)),
      ((valBits V, epochHashSpace U w N), (lmSubWords N w, effBucketPosBits N)))
    let prog := writeCompABProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteCompABPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = offCompGM U w N ∧
    s'.frontier = s.frontier ∧
    (∀ (j : ℕ) (hj : j < 16),
      s'.mem (dstMetaBase + 27 + j) = mkCompParams U V w N ⟨j, by omega⟩) ∧
    (∀ a, ¬(dstMetaBase + 27 ≤ a ∧ a < dstMetaBase + 43) → s'.mem a = s.mem a) ∧
    memoryCost prog s = 16 := by
  intro d prog s'
  obtain ⟨_, hvA, hresA, hfrA, hmA, hframeA, hcA⟩ :=
    writeCompSubAProg_spec (s := s) hw hN hNU hU hV h63 hfit_dst
  set sA := (Memory.spec 0).clientState s (writeCompSubAProg
    (((dstMetaBase + 27, w), (N, quotientBits U N)),
     (valBits V, (epochHashSpace U w N, lmSubWords N w))))
  obtain ⟨_, hvB, hresB, hfrB, hmB, hframeB, hcB⟩ :=
    writeCompSubBProg_spec (s := sA) hw hN hNU hU hV (hfrA.symm ▸ h63) hfit_dst
  set sB := (Memory.spec 0).clientState sA (writeCompSubBProg
    ((dstMetaBase + 27, offCompLMSub U w N 3), (lmSubWords N w, effBucketPosBits N)))
  have hs'_eq : s' = sB := by
    dsimp only [s', prog, d, writeCompABProg]
    rw [StateTransitionSpec.clientState_bind, hresA]
  refine ⟨⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeCompABProg]
    rw [validHistory_bind', hresA]; exact ⟨hvA, hvB⟩
  · dsimp only [prog, d, writeCompABProg]
    rw [prog_clientResult_bind, hresA]; exact hresB
  · rw [hs'_eq, hfrB, hfrA]
  · intro j hj
    rw [hs'_eq]
    by_cases hj8 : j < 8
    · rw [hframeB _ (by omega)]; exact hmA j hj8
    · have hB := hmB (j - 8) (by omega)
      rw [show dstMetaBase + 35 + (j - 8) = dstMetaBase + 27 + j by omega] at hB
      exact hB.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
  · intro a ha
    rw [hs'_eq, hframeB a (by omega), hframeA a (by omega)]
  · dsimp only [prog, d, writeCompABProg]
    rw [Realization.memoryCost_bind', hresA, hcA, hcB]

private theorem realizesBounded_writeCompAB :
    RealizesBounded .exact writeCompABProg
      (WordEncoding.encode (α := Tup4 × Tup4)) (WordEncoding.encode (α := ℕ))
      WriteCompABPre (fun _ _ => 0) := by
  have hA := realizesBounded_writeCompSubA
  have hB := realizesBounded_writeCompSubB
  realize
  · rcases d with ⟨⟨⟨cpBase, wVal⟩, ⟨N, qBitsVal⟩⟩, ⟨⟨vBits, hSpace⟩, ⟨lmSubW, lmBits⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, hwVal, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    subst wVal
    exact ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩
  · rcases d with ⟨⟨⟨cpBase, wVal⟩, ⟨N, qBitsVal⟩⟩, ⟨⟨vBits, hSpace⟩, ⟨lmSubW, lmBits⟩⟩⟩
    obtain ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, hwVal, rfl, rfl, rfl, rfl, rfl,
      h63, hfit_dst⟩ := h
    subst wVal
    obtain ⟨_, _, hresA, hfrA, _, _, _⟩ :=
      writeCompSubAProg_spec (s := s) hw hN hNU hU hV h63 hfit_dst
    dsimp only at *
    rw [hresA]
    exact ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl,
      hfrA.symm ▸ h63, hfit_dst⟩

/-- Compute and write the 36-word `mkCompParams U V w N` block at `[dstMetaBase + 27, +36)`,
returning `offCompItems U w N`. -/
private def writeCompParamsSubProg :
    (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace)))) => do
    let ((bBits, lmBits), ((numMicro, minCap), (sSize, (maxTail, gmSlabMeta)))) ←
      writeCompScalesGmDProg ((dstMetaBase, N), (logN, llf))
    let (lmSubW, (gmWords, tailWords)) ←
      computeMetaWordsProg
        (((wVal, N), (bBits, lmBits)), ((logN, sSize), (maxTail, gmSlabMeta)))
    let cpBase := dstMetaBase + 27
    let offGM ← writeCompABProg
      (((cpBase, wVal), (N, qBitsVal)), ((vBits, hSpace), (lmSubW, lmBits)))
    let offItemsVal ← writeCompSubCProg
      (((cpBase, offGM), (gmWords, tailWords)), ((logN, maxTail), (bBits, sSize)))
    writeCompSubEProg (cpBase, ((numMicro, minCap), (offItemsVal, hSpace)))
    pure offItemsVal

private def WriteCompParamsSubPre (w : ℕ) :
    (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace)))), s =>
    ∃ U V,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ vBits = valBits V ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      hSpace = epochHashSpace U w N ∧
      dstMetaBase + 63 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

private theorem writeCompParamsSubProg_props {w U V dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (h63 : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((dstMetaBase, (w, N)), ((quotientBits U N, valBits V),
      (Nat.log 2 N, (Dynamic.logLogFactor N, epochHashSpace U w N))))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeCompParamsSubProg d)) ∧
    (Memory.spec 0).clientResult s (writeCompParamsSubProg d) = offCompItems U w N ∧
    ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).frontier = s.frontier ∧
    (∀ i : Fin 36,
      ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).mem
        (dstMetaBase + offCompParams + i.val) = mkCompParams U V w N i) ∧
    (∀ a, ¬(dstMetaBase + offCompParams ≤ a ∧ a < dstMetaBase + offScratch) →
      ((Memory.spec 0).clientState s (writeCompParamsSubProg d)).mem a = s.mem a) ∧
    memoryCost (writeCompParamsSubProg d) s ≤ N + 40 := by
  intro d
  obtain ⟨_, hvD, hresD, hfrD, hmD, hframeD, hcD⟩ :=
    writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
  set sD := (Memory.spec 0).clientState s
    (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
  obtain ⟨hv_mw, hst_mw, hres_mw, hc_mw⟩ :=
    computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
  obtain ⟨_, hvAB, hresAB, hfrAB, hmAB, hframeAB, hcAB⟩ :=
    writeCompABProg_spec (s := sD) hw hN hNU hU hV (hfrD.symm ▸ h63) hfit_dst
  set sAB := (Memory.spec 0).clientState sD (writeCompABProg
    (((dstMetaBase + 27, w), (N, quotientBits U N)),
     ((valBits V, epochHashSpace U w N), (lmSubWords N w, effBucketPosBits N))))
  obtain ⟨_, hvC, hresC, hfrC, hmC, hframeC, hcC⟩ :=
    writeCompSubCProg_spec (s := sAB) hw hN hNU hU hV (hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
  set sC := (Memory.spec 0).clientState sAB (writeCompSubCProg
    (((dstMetaBase + 27, offCompGM U w N),
      (packedWords (globalMetaLen N) (globalPtrBits N) w,
       packedWords (maxTailItems N) (globalPtrBits N) w)),
     ((Nat.log 2 N, maxTailItems N), (bucketBits N, slabSize N))))
  obtain ⟨_, hvE, hfrE, hmE, hframeE, hcE⟩ :=
    writeCompSubEProg_spec (V := V) (s := sC) hw hNU hU hV
      (hfrC.symm ▸ hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
  set sE := (Memory.spec 0).clientState sC (writeCompSubEProg
    (dstMetaBase + 27,
      ((numMicroPerBucket N, min N (effBucketCap N)),
       (offCompItems U w N, epochHashSpace U w N))))
  have hs_final : (Memory.spec 0).clientState s (writeCompParamsSubProg d) = sE := by
    dsimp only [d, writeCompParamsSubProg]
    rw [StateTransitionSpec.clientState_bind, hresD]; dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_mw, hres_mw]; dsimp only
    rw [StateTransitionSpec.clientState_bind, hresAB,
      StateTransitionSpec.clientState_bind, hresC,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [d, writeCompParamsSubProg]
    rw [validHistory_bind', hresD]; refine ⟨hvD, ?_⟩
    dsimp only; rw [validHistory_bind', hst_mw, hres_mw]; refine ⟨hv_mw, ?_⟩
    dsimp only; rw [validHistory_bind', hresAB]; refine ⟨hvAB, ?_⟩
    rw [validHistory_bind', hresC]; refine ⟨hvC, ?_⟩
    rw [validHistory_bind']; exact ⟨hvE, trivial⟩
  · dsimp only [d, writeCompParamsSubProg]
    rw [prog_clientResult_bind, hresD]; dsimp only
    rw [prog_clientResult_bind, hst_mw, hres_mw]; dsimp only
    rw [prog_clientResult_bind, hresAB, prog_clientResult_bind, hresC,
      prog_clientResult_bind, prog_clientResult_pure]
  · rw [hs_final, hfrE, hfrC, hfrAB, hfrD]
  · intro ⟨j, hj⟩
    rw [hs_final]
    dsimp only [offCompParams]
    by_cases hj16 : j < 16
    · rw [hframeE _ (by omega), hframeC _ (by omega)]; exact hmAB j hj16
    · by_cases hj24 : j < 24
      · rw [hframeE _ (by omega)]
        have hC := hmC (j - 16) (by omega)
        rw [show dstMetaBase + 43 + (j - 16) = dstMetaBase + 27 + j by omega] at hC
        exact hC.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
      · by_cases hj32 : j < 32
        · rw [hframeE _ (by omega), hframeC _ (by omega), hframeAB _ (by omega)]
          have hD := hmD (j - 24) (by omega)
          rw [show dstMetaBase + 51 + (j - 24) = dstMetaBase + 27 + j by omega] at hD
          exact hD.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
        · have hE := hmE (j - 32) (by omega)
          rw [show dstMetaBase + 59 + (j - 32) = dstMetaBase + 27 + j by omega] at hE
          exact hE.trans (congrArg _ (Fin.ext (by dsimp only; omega)))
  · intro a ha
    rw [hs_final]
    unfold offCompParams offScratch at ha
    rw [hframeE a (by omega), hframeC a (by omega), hframeAB a (by omega), hframeD a (by omega)]
  · dsimp only [d, writeCompParamsSubProg]
    rw [Realization.memoryCost_bind', hresD]; dsimp only
    rw [Realization.memoryCost_bind', hst_mw, hres_mw]; dsimp only
    rw [Realization.memoryCost_bind', hresAB, Realization.memoryCost_bind', hresC,
      Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeCompScalesGmDProg _) s +
      (memoryCost (computeMetaWordsProg _) sD +
        (memoryCost (writeCompABProg _) sD +
          (memoryCost (writeCompSubCProg _) sAB +
            (memoryCost (writeCompSubEProg _) sC + 0)))) ≤ _
    omega

private theorem realizesBounded_writeCompParamsSub :
    RealizesBounded .exact writeCompParamsSubProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      WriteCompParamsSubPre (fun _ _ => 0) := by
  have hD := realizesBounded_writeCompScalesGmD
  have hmw := realizesBounded_computeMetaWords
  have hAB := realizesBounded_writeCompAB
  have hC := realizesBounded_writeCompSubC
  have hE := realizesBounded_writeCompSubE
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, ⟨wVal, N⟩⟩, ⟨⟨qBitsVal, vBits⟩, ⟨logN, ⟨llf, hSpace⟩⟩⟩⟩
    obtain ⟨U, V, hw, hN, hNU, hU, hV, hwVal, rfl, rfl, rfl, rfl, rfl, h63, hfit_dst⟩ := h
    subst wVal
    dsimp only at *
    have hfit63 : Fits w (dstMetaBase + 63) :=
      hfit_dst.of_le (by
        unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega))
  all_goals try exact hfit63.of_le (by omega)
  · exact ⟨U, hw, hN, hNU, hU, rfl, rfl, h63, hfit_dst⟩
  · obtain ⟨_, _, hresD, _, _, _, _⟩ :=
      writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
    rw [hresD]; dsimp only
    exact ⟨U, dstMetaBase, hw, hN, hNU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfit_dst⟩
  · obtain ⟨_, _, hresD, hfrD, _, _, _⟩ :=
      writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
    set sD := (Memory.spec 0).clientState s
      (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
    obtain ⟨_, hst_mw, hres_mw, _⟩ :=
      computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
    rw [hresD]; dsimp only
    rw [hst_mw, hres_mw]; dsimp only
    exact ⟨U, V, dstMetaBase, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hfrD.symm ▸ h63, hfit_dst⟩
  · obtain ⟨_, _, hresD, hfrD, _, _, _⟩ :=
      writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
    set sD := (Memory.spec 0).clientState s
      (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
    obtain ⟨_, hst_mw, hres_mw, _⟩ :=
      computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
    obtain ⟨_, _, hresAB, hfrAB, _, _, _⟩ :=
      writeCompABProg_spec (s := sD) hw hN hNU hU hV (hfrD.symm ▸ h63) hfit_dst
    rw [hresD]; dsimp only
    rw [hst_mw, hres_mw]; dsimp only
    rw [hresAB]
    exact ⟨U, V, dstMetaBase, N, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hfrAB.symm ▸ hfrD.symm ▸ h63, hfit_dst⟩
  · obtain ⟨_, _, hresD, hfrD, _, _, _⟩ :=
      writeCompScalesGmDProg_spec (V := V) (s := s) hw hN hNU hU hV h63 hfit_dst
    set sD := (Memory.spec 0).clientState s
      (writeCompScalesGmDProg ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N)))
    obtain ⟨_, hst_mw, hres_mw, _⟩ :=
      computeMetaWordsProg_spec (s := sD) hw hN hNU hU hfit_dst
    obtain ⟨_, _, hresAB, hfrAB, _, _, _⟩ :=
      writeCompABProg_spec (s := sD) hw hN hNU hU hV (hfrD.symm ▸ h63) hfit_dst
    set sAB := (Memory.spec 0).clientState sD (writeCompABProg
      (((dstMetaBase + 27, w), (N, quotientBits U N)),
       ((valBits V, epochHashSpace U w N), (lmSubWords N w, effBucketPosBits N))))
    obtain ⟨_, _, hresC, hfrC, _, _, _⟩ :=
      writeCompSubCProg_spec (s := sAB) hw hN hNU hU hV (hfrAB.symm ▸ hfrD.symm ▸ h63) hfit_dst
    rw [hresD]; dsimp only
    rw [hst_mw, hres_mw]; dsimp only
    rw [hresAB, hresC]
    exact ⟨U, dstMetaBase, N, rfl, by rw [hfrC]; exact hfrAB.symm ▸ hfrD.symm ▸ h63, hfit_dst⟩

/-- Populate the 8-word root header, 19-word `HashParams`, and 36-word `CompParams` at
`[dstMetaBase, dstMetaBase + 63)` from `[srcHdrBase, srcHdrBase + 5)` and `(N, n_cur, n_init_new)`,
returning `(offCompItems U w N, epochHashSpace U w N)` (`¬ReadsWidth`). -/
def writeEpochParamsGenProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × ℕ)
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))) => do
    let (wVal, (kBits, vBits)) ←
      writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let (logN, (qBitsVal, llf)) ← computeLogScalesProg (dstMetaBase, (N, kBits))
    let hSpace ← writeHashParamsSubProg ((dstMetaBase, dstMetaBase), (wVal, (qBitsVal, logN)))
    let offItemsVal ← writeCompParamsSubProg
      ((dstMetaBase, (wVal, N)), ((qBitsVal, vBits), (logN, (llf, hSpace))))
    pure (offItemsVal, hSpace)

/-- Entry precondition for `writeEpochParamsGenProg`. -/
@[expose] def WriteEpochParamsPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))), s =>
    ∃ U V N_old n_old n_init_old,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ V ≤ 2 ^ w ∧
      Fits w n_cur ∧ Fits w n_init_new ∧
      RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem ∧
      srcHdrBase + 5 ≤ s.frontier ∧
      dstMetaBase + 63 ≤ s.frontier ∧
      Fits w (dstMetaBase + offCompItems U w N)

theorem writeEpochParamsGenProg_spec
    {w U V N_old n_old n_init_old srcHdrBase dstMetaBase N n_cur n_init_new : ℕ}
    {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hV : V ≤ 2 ^ w)
    (hfit_ncur : Fits w n_cur) (hfit_ninit : Fits w n_init_new)
    (hhdr : RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem)
    (hsrc_fr : srcHdrBase + 5 ≤ s.frontier)
    (hdst_fr : dstMetaBase + 63 ≤ s.frontier)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let prog := writeEpochParamsGenProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteEpochParamsPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = (offCompItems U w N, epochHashSpace U w N) ∧
    s'.frontier = s.frontier ∧
    RootHeaderValid U V w N n_cur n_init_new dstMetaBase s'.mem ∧
    EpochParamsStored U V w N dstMetaBase s'.mem ∧
    (∀ a, ¬(dstMetaBase ≤ a ∧ a < dstMetaBase + offScratch) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ 11 * N + 100 := by
  intro d prog s'
  have hU := hhdr.fits_U
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hdst8 : dstMetaBase + 8 ≤ s.frontier := by omega
  obtain ⟨_, hv_r, hres_r, hfr_r, hhdr_r, hframe_r, hc_r⟩ :=
    writeRootHdrSubProg_spec hhdr hV (hU.of_le hNU) hfit_ncur hfit_ninit (h225.of_le (by decide))
      hsrc_fr hdst8
  set s1 := (Memory.spec 0).clientState s
    (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
  have hdst_fr1 : dstMetaBase + 63 ≤ s1.frontier := hfr_r.symm ▸ hdst_fr
  have hdst_lt1 : dstMetaBase < s1.frontier := by omega
  obtain ⟨hv_ls, hst_ls, hres_ls, hc_ls⟩ :=
    computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
  obtain ⟨hv_hp, hres_hp, hfr_hp, hmem_hp, hframe_hp, hc_hp⟩ :=
    writeHashParamsSubProg_props (s := s1) hw hN hNU hU hdst_lt1 (by omega) hfit_dst
  set s2 := (Memory.spec 0).clientState s1
    (writeHashParamsSubProg ((dstMetaBase, dstMetaBase), (w, (quotientBits U N, Nat.log 2 N))))
  have hdst_fr2 : dstMetaBase + 63 ≤ s2.frontier := hfr_hp.symm ▸ hdst_fr1
  obtain ⟨hv_cp, hres_cp, hfr_cp, hmem_cp, hframe_cp, hc_cp⟩ :=
    writeCompParamsSubProg_props (s := s2) hw hN hNU hU hV hdst_fr2 hfit_dst
  set s3 := (Memory.spec 0).clientState s2
    (writeCompParamsSubProg ((dstMetaBase, (w, N)),
      ((quotientBits U N, valBits V),
        (Nat.log 2 N, (Dynamic.logLogFactor N, epochHashSpace U w N)))))
  have hs'_eq : s' = s3 := by
    dsimp only [s', prog, d, writeEpochParamsGenProg]
    rw [StateTransitionSpec.clientState_bind, hres_r]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hst_ls, hres_ls]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hres_hp, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, V, N_old, n_old, n_init_old, hw, hN, hNU, hV, hfit_ncur, hfit_ninit, hhdr,
      hsrc_fr, hdst_fr, hfit_dst⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [validHistory_bind']; refine ⟨hv_r, ?_⟩
    rw [hres_r]; dsimp only
    rw [validHistory_bind']; refine ⟨hv_ls, ?_⟩
    rw [hst_ls, hres_ls]; dsimp only
    rw [validHistory_bind']; refine ⟨hv_hp, ?_⟩
    rw [hres_hp, validHistory_bind']; exact ⟨hv_cp, trivial⟩
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [prog_clientResult_bind, hres_r]
    change (Memory.spec 0).clientResult s1 _ = _
    dsimp only
    rw [prog_clientResult_bind, hst_ls, hres_ls]
    dsimp only
    rw [prog_clientResult_bind, hres_hp]
    change (Memory.spec 0).clientResult s2 _ = _
    rw [prog_clientResult_bind, hres_cp, prog_clientResult_pure]
  · rw [hs'_eq, hfr_cp, hfr_hp, hfr_r]
  · rw [hs'_eq]
    have h0_7 : ∀ j < 8, s3.mem (dstMetaBase + j) = s1.mem (dstMetaBase + j) := fun j hj => by
      rw [hframe_cp _ (by unfold offCompParams offScratch; omega),
        hframe_hp _ (by unfold offHashParams offCompParams; omega)]
    exact ⟨hhdr_r.fits_U, hhdr_r.pos_U, hhdr_r.pos_V,
      by simpa using (h0_7 0 (by decide)).trans hhdr_r.hdr_U,
      (h0_7 1 (by decide)).trans hhdr_r.hdr_V,
      (h0_7 2 (by decide)).trans hhdr_r.hdr_w,
      (h0_7 3 (by decide)).trans hhdr_r.hdr_keyBits,
      (h0_7 4 (by decide)).trans hhdr_r.hdr_valBits,
      (h0_7 5 (by decide)).trans hhdr_r.hdr_N,
      (h0_7 6 (by decide)).trans hhdr_r.hdr_n,
      (h0_7 7 (by decide)).trans hhdr_r.hdr_n_init⟩
  · rw [hs'_eq]
    refine ⟨fun i => ?_, hmem_cp⟩
    rw [hframe_cp _ (by have := i.isLt; unfold offHashParams offCompParams offScratch; omega)]
    exact hmem_hp i
  · intro a ha
    rw [hs'_eq, hframe_cp a (by unfold offCompParams offScratch at *; omega),
      hframe_hp a (by unfold offHashParams offCompParams offScratch at *; omega),
      hframe_r a (by unfold offScratch at ha; omega)]
  · dsimp only [prog, d, writeEpochParamsGenProg]
    rw [Realization.memoryCost_bind', hres_r, Realization.memoryCost_bind', hst_ls, hres_ls]
    dsimp only
    rw [Realization.memoryCost_bind', hres_hp, Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (writeRootHdrSubProg _) s +
      (memoryCost (computeLogScalesProg _) s1 +
        (memoryCost (writeHashParamsSubProg _) s1 +
          (memoryCost (writeCompParamsSubProg _) s2 + 0))) ≤ _
    omega

theorem realizesBounded_writeEpochParamsGen :
    RealizesBounded .exact writeEpochParamsGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      WriteEpochParamsPre (fun _ _ => 0) := by
  have hr := realizesBounded_writeRootHdrSub
  have hls := realizesBounded_computeLogScales
  have hhp := realizesBounded_writeHashParamsSub
  have hcp := realizesBounded_writeCompParamsSub
  realize
  all_goals (
    rcases d with ⟨⟨srcHdrBase, dstMetaBase⟩, ⟨N, ⟨n_cur, n_init_new⟩⟩⟩
    obtain ⟨U, V, N_old, n_old, n_init_old, hw, hN, hNU, hV, hnc, hni, hhdr,
      hsrc_fr, hdst_fr, hfit_dst⟩ := h
    dsimp only at *
    have hU := hhdr.fits_U
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hdst8 : dstMetaBase + 8 ≤ s.frontier := by omega
    obtain ⟨hpre_r, _, hres_r, hfr_r, _, _, _⟩ :=
      writeRootHdrSubProg_spec hhdr hV (hU.of_le hNU) hnc hni (h225.of_le (by decide))
        hsrc_fr hdst8)
  · exact hpre_r
  · rw [hres_r]
    exact ⟨U, hw, hN, hNU, hU, rfl, by rw [hfr_r]; omega, h225⟩
  · rw [hres_r]
    set s1 := (Memory.spec 0).clientState s
      (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
    have hdst_lt1 : dstMetaBase < s1.frontier := by rw [hfr_r]; omega
    obtain ⟨_, hst_ls, hres_ls, _⟩ :=
      computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
    rw [hst_ls, hres_ls]
    exact ⟨U, N, hw, hN, hNU, hU, rfl, rfl, rfl, hdst_lt1, by rw [hfr_r]; omega, hfit_dst⟩
  · rw [hres_r]
    set s1 := (Memory.spec 0).clientState s
      (writeRootHdrSubProg ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))))
    have hdst_lt1 : dstMetaBase < s1.frontier := by rw [hfr_r]; omega
    obtain ⟨_, hst_ls, hres_ls, _⟩ :=
      computeLogScalesProg_exec (s := s1) hw hN hNU hU hdst_lt1 h225
    rw [hst_ls, hres_ls]
    obtain ⟨_, hres_hp, hfr_hp, _, _, _⟩ :=
      writeHashParamsSubProg_props (s := s1) hw hN hNU hU hdst_lt1 (by rw [hfr_r]; omega) hfit_dst
    rw [hres_hp]
    exact ⟨U, V, hw, hN, hNU, hU, hV, rfl, rfl, rfl, rfl, rfl, rfl,
      hfr_hp.symm ▸ hfr_r.symm ▸ hdst_fr, hfit_dst⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
