/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-Tape `1 · OPT` Shared Migration Arena and Peak-Space Bounds

This module defines the shared single-tape item arena (`migrateArenaWords`) and peak migration
word footprint (`migratePeakWords`) for epoch capacity migration in the resizable succinct dynamic
dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA
2024][BenderFarachColtonKuszmaulKuszmaul2024]; [Kuszmaul, Liang, and Zhou, SODA
2026][KuszmaulLiangZhou2026]), proving:

* word-level non-overlap (`newItemEnd_le_oldItemNextWord`) between written new items `[0, j)` and
  unread right-aligned old items `[j, n)` across both growing and shrinking epochs;
* `1 · OPT` succinct word and bit bounds (`migratePeakWords_le_succinctWords`,
  `w_mul_migratePeakWords_le_bits`);
* parameter-free `O(n)` linear word bounds (`compactedItemWords_le_linear`,
  `offCompItems_le_linear`, `migratePeakWords_le_linear`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migrateArenaWords`,
  `migratePeakWords`: shared single-tape item-arena length and peak migration word footprint.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.newItemEnd_le_oldItemNextWord`:
  word-level non-overlap between written new items and unread right-aligned old items.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.migratePeakWords_le_succinctWords`,
  `w_mul_migratePeakWords_le_bits`, `migratePeakWords_le_linear`: `1 · OPT` succinct space bounds
  and parameter-free `O(n)` linear word bound.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

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

/-- Sum of floor divisions is at most floor division of the sum for `0 < w`. -/
theorem div_add_div_le {a b w : ℕ} (hw : 0 < w) :
    a / w + b / w ≤ (a + b) / w := by
  exact (Nat.le_div_iff_mul_le hw).mpr (by nlinarith [Nat.mul_div_le a w, Nat.mul_div_le b w])

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
    rw [← wOffQ_mul_add_bOffQ (q_bits := quotientBits U N_old) (v_bits := valBits V) (w := w)
      (d := j), Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt (bOffQ_lt hw), add_zero]
  rw [hwo_eq]
  have hj_iw : compactedItemWords U V w N_new j ≤ (j * S_new) / w + 3 :=
    Nat.add_le_add_right (div_ceil_le_div_add_one hw) 2
  have hold_iw : compactedItemWords U V w N_old n ≤ (n * S_old) / w + 3 :=
    Nat.add_le_add_right (div_ceil_le_div_add_one hw) 2
  have hnew_iw : (n * S_new) / w + 2 ≤ compactedItemWords U V w N_new n :=
    Nat.add_le_add_right (Nat.div_le_div_right (by omega : n * S_new ≤ n * S_new + w - 1)) 2
  unfold migrateArenaWords
  rcases le_total S_new S_old with hle | hge
  · have := Nat.div_le_div_right (c := w) (Nat.mul_le_mul_left j hle)
    omega
  · have hconv : j * S_new + n * S_old ≤ n * S_new + j * S_old := by
      nlinarith [Nat.mul_le_mul_left (n - j) hge, Nat.add_sub_of_le hj]
    have := (div_add_div_le hw).trans ((Nat.div_le_div_right hconv).trans
      (Nat.add_div_le_div_add_div_add_one _ _ w))
    omega

/-- Shared metadata bit-packing bound `offCompItems U w N ≤ ⌈84 N log log N / w⌉ + 439` used by
both the `1 · OPT` succinct bound and the parameter-free `O(N)` linear word bound. -/
private theorem offCompItems_le_div_eightyFour_logLog {U w N : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    offCompItems U w N ≤ (84 * N * Dynamic.logLogFactor N + w - 1) / w + 439 := by
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
  have h84N : (2 * N) * 1 + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N ≤
      84 * N * Dynamic.logLogFactor N := by
    nlinarith [Dynamic.one_le_logLogFactor N, localMetaLen_mul_effBucketPosBits_le N,
      globalMetaLen_mul_globalPtrBits_le N, maxTailItems_mul_globalPtrBits_le N]
  exact hmeta_le.trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 439)

/-- Compacted metadata word offset bound in terms of `n` when `N ≤ 4 * n`. -/
theorem offCompItems_le_div_metaBits {U w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) (hN4 : N ≤ 4 * n) :
    offCompItems U w N ≤ (1344 * n * Dynamic.logLogFactor n + w - 1) / w + 439 := by
  have hbase := offCompItems_le_div_eightyFour_logLog hw hNU hU
  have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
    (Dynamic.logLogFactor_mono hN4).trans (Dynamic.logLogFactor_four_mul_le n)
  have hN_ll : N * Dynamic.logLogFactor N ≤ 16 * (n * Dynamic.logLogFactor n) := by
    calc N * Dynamic.logLogFactor N
        ≤ (4 * n) * (4 * Dynamic.logLogFactor n) := Nat.mul_le_mul hN4 hll_N
      _ = 16 * (n * Dynamic.logLogFactor n) := by ring
  have h1344 : 84 * N * Dynamic.logLogFactor N ≤ 1344 * n * Dynamic.logLogFactor n := by nlinarith
  exact hbase.trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 439)

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
  have h6n : 6 * n ≤ 6 * n * Dynamic.logLogFactor n := Nat.le_mul_of_pos_right _ hll_n
  have hnum0 : n * (quotientBits U N + valBits V) ≤
      Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by nlinarith
  unfold compactedItemWords
  exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 2

private theorem div_ceil_add_div_ceil_le {A B w : ℕ} (hw : 0 < w) :
    (A + w - 1) / w + (B + w - 1) / w ≤ (A + B + w - 1) / w + 1 := by
  exact (div_add_div_le hw).trans ((Nat.div_le_div_right (by omega)).trans_eq
    (Nat.add_mul_div_right (A + B + w - 1) 1 hw))

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
      have har : migrateArenaWords U V w N_old (targetCap U n) n ≤
          (Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n + w - 1) / w + 8 :=
        Nat.add_le_add_right (max_le (compactedItemWords_le_div_optBits U V w hn_old hN4_old)
          (compactedItemWords_le_div_optBits U V w hn_new hN4_new)) 6
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
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (Nat.sub_lt hw zero_lt_one),
          Nat.zero_add]

private theorem logLogFactor_le_three_mul_w {w N : ℕ} (hw : 0 < w) (hN : Fits w N) :
    Dynamic.logLogFactor N ≤ 3 * w := by
  unfold Dynamic.logLogFactor
  have hmax : max N 4 ≤ 2 ^ (w + 2) := by
    refine max_le (hN.le.trans (Nat.pow_le_pow_right two_pos (by omega))) ?_
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right two_pos (by omega)
  have hc1 : Nat.clog 2 (max N 4) ≤ w + 2 :=
    (Nat.clog_le_iff_le_pow one_lt_two).mpr hmax
  exact (Nat.clog_mono_right 2 hc1).trans
    ((Nat.clog_le_iff_le_pow one_lt_two).mpr (by linarith [@Nat.lt_two_pow_self (3 * w)]))

/-- Parameter-free `O(N)` word bound on `offCompItems U w N` (`≤ 252 * N + 439`) for all
`0 < w`, `N ≤ U`, and `Fits w U`, independent of `(U, V, w)`. -/
theorem offCompItems_le_linear {U w N : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U) :
    offCompItems U w N ≤ 252 * N + 439 := by
  have hbase := offCompItems_le_div_eightyFour_logLog hw hNU hU.le
  have hll_w : Dynamic.logLogFactor N ≤ 3 * w := logLogFactor_le_three_mul_w hw (hU.of_le hNU)
  have h252_0 : 84 * N * Dynamic.logLogFactor N ≤ (252 * N) * w := by
    calc 84 * N * Dynamic.logLogFactor N
        ≤ 84 * N * (3 * w) := Nat.mul_le_mul_left (84 * N) hll_w
      _ = (252 * N) * w := by ring
  have hdiv : (84 * N * Dynamic.logLogFactor N + w - 1) / w ≤ 252 * N := by
    calc _ ≤ ((w - 1) + (252 * N) * w) / w := Nat.div_le_div_right (by omega)
      _ = 252 * N := by
          rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (Nat.sub_lt hw zero_lt_one),
            Nat.zero_add]
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
    have htc : targetCap U n = min (2 * n) U := by
      unfold targetCap
      exact ite_eq_right (by omega)
    have hm_old := (offCompItems_le_linear hw hNU_old hU).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 252 hN4_old) 439)
    have hm_new := (offCompItems_le_linear hw (htc ▸ min_le_right _ _) hU).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 252 (htc ▸ min_le_left _ _)) 439)
    have har : migrateArenaWords U V w N_old (targetCap U n) n ≤ 2 * n + 8 :=
      Nat.add_le_add_right (max_le (compactedItemWords_le_linear hw hU.le hV)
        (compactedItemWords_le_linear hw hU.le hV)) 6
    unfold migratePeakWords
    omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
