/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.BerExp
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Falcon v1.2 BerExp lazy-byte trace

Falcon v1.2 Algorithm 14 compares a uniform 64-bit word with its threshold one byte at a time,
most significant byte first, and stops at the first mismatch. This module formalizes that
operational boundary after the threshold has already been computed. `berExpLazyCoin` makes one
eight-fair-bit draw for every visited byte, returns the same decision as the fixed 64-bit
experiment in `BerExp.lean`, and records the number of bytes read.

The trace uses between one and eight bytes. It uses more than one byte exactly when the first
random byte equals the first threshold byte, an event of probability `2^-8`; equality in all
eight bytes consumes all eight bytes and rejects. No claim is made about PRNG-buffer refills,
native instructions, running time, circuit or static-program size.

As in `BerExp.lean`, the input is already an exact 64-bit threshold. This module does not
formalize `ApproxExp`'s floating-point error, `BaseSampler`, `SamplerZ`, a Gaussian law or retry
termination, a security reduction, or the still-developing FN-DSA / FIPS 206 interface.

## Main definitions

* `Cslib.Crypto.Falcon.BerExpLazyResult`: the decision and number of bytes read.
* `Cslib.Crypto.Falcon.berExpLazyTrace`: the deterministic first-mismatch trace on byte values.
* `Cslib.Crypto.Falcon.berExpThresholdBytes`: the threshold's eight big-endian byte values.
* `Cslib.Crypto.Falcon.berExpLazyCoin`: the sequential lazy-byte experiment.

## Main results

* `Cslib.Crypto.Falcon.berExpLazyTrace_accepted`: equal-length traces implement strict
  lexicographic comparison.
* `Cslib.Crypto.Falcon.berExpLazyTrace64_accepted`: on two 64-bit words the trace implements the
  same strict comparison as `berExpThresholdAccepts`.
* `Cslib.Crypto.Falcon.eval_berExpLazyCoin_accepted`: the lazy and fixed 64-bit experiments have
  the same decision distribution.
* `Cslib.Crypto.Falcon.mem_support_berExpLazyCoin_bytesRead`: every possible run reads between
  one and eight bytes.
* `Cslib.Crypto.Falcon.eval_berExpLazyCoin_bytesRead_gt_one`: the probability of reading past the
  first byte is exactly `2^-8`.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Section 3.9.3, Algorithm 14, lines 5--10, printed p. 43.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/sign.c::BerExp`, lines 1082--1087.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/inner.h::prng_get_u8`, lines 565--577.
-/

public section

namespace Cslib.Crypto.Falcon

open Probability

/-- The observable result of Algorithm 14's lazy comparison.

`accepted` is the comparison result. `bytesRead` counts eight-bit PRNG outputs consumed by the
comparison itself; it does not count buffer refills or any preceding `BaseSampler` draw. -/
structure BerExpLazyResult where
  /-- Whether the sampled 64-bit word is strictly below the threshold. -/
  accepted : Bool
  /-- The number of consecutive random bytes inspected before stopping. -/
  bytesRead : Nat
  deriving DecidableEq

private def BerExpLazyResult.stop (accepted : Bool) : BerExpLazyResult :=
  { accepted, bytesRead := 1 }

private def BerExpLazyResult.next (result : BerExpLazyResult) : BerExpLazyResult :=
  { result with bytesRead := result.bytesRead + 1 }

/-- Compare byte values from left to right, stopping at the first mismatch.

The source-faithful use has two lists of eight values below `256`. The definition is total on
arbitrary lists: exhaustion before a mismatch rejects, and every matched pair is counted. -/
@[expose] def berExpLazyTrace : List Nat → List Nat → BerExpLazyResult
  | threshold :: thresholds, sample :: samples =>
      if sample < threshold then
        BerExpLazyResult.stop true
      else if threshold < sample then
        BerExpLazyResult.stop false
      else
        (berExpLazyTrace thresholds samples).next
  | _, _ => { accepted := false, bytesRead := 0 }

/-- On lists of equal length, the lazy trace accepts exactly at strict lexicographic comparison. -/
theorem berExpLazyTrace_accepted {thresholds samples : List Nat}
    (hlength : thresholds.length = samples.length) :
    (berExpLazyTrace thresholds samples).accepted = decide (samples < thresholds) := by
  induction thresholds generalizing samples with
  | nil =>
      obtain rfl : samples = [] := List.length_eq_zero_iff.mp hlength.symm
      rfl
  | cons threshold thresholds ih =>
      obtain ⟨sample, samples, rfl⟩ := List.exists_cons_of_length_eq_add_one hlength.symm
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength
      rcases lt_trichotomy sample threshold with hlt | heq | hgt
      · simp [berExpLazyTrace, hlt]
      · subst sample
        simp [berExpLazyTrace, ih hlength]
      · simp [berExpLazyTrace, hgt, hgt.asymm]

/-- A deterministic trace cannot read more pairs than either input supplies. -/
theorem berExpLazyTrace_bytesRead_le (thresholds samples : List Nat) :
    (berExpLazyTrace thresholds samples).bytesRead ≤ min thresholds.length samples.length := by
  induction thresholds generalizing samples with
  | nil => simp [berExpLazyTrace]
  | cons threshold thresholds ih =>
      cases samples with
      | nil => simp [berExpLazyTrace]
      | cons sample samples =>
          by_cases hlt : sample < threshold
          · simp [berExpLazyTrace, hlt]
          · by_cases hgt : threshold < sample
            · simp [berExpLazyTrace, hlt, hgt]
            · simp only [berExpLazyTrace, hlt, hgt, if_false, BerExpLazyResult.next]
              have := ih samples
              omega

/-- Supplying at least one pair makes the trace inspect at least its first byte. -/
theorem one_le_berExpLazyTrace_bytesRead (threshold thresholds sample : Nat)
    (samples : List Nat) :
    1 ≤ (berExpLazyTrace (threshold :: thresholds) (sample :: samples)).bytesRead := by
  by_cases hlt : sample < threshold
  · simp [berExpLazyTrace, hlt, BerExpLazyResult.stop]
  · by_cases hgt : threshold < sample
    · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.stop]
    · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.next]

/-- The eight most-significant-first byte values of a 64-bit threshold. -/
@[expose] def berExpThresholdBytes (threshold : BerExpThreshold) : List Nat :=
  (BitString.listRows 8 8 (BitString.binaryWord 64 threshold.val)).map
    BitString.binaryValue

/-- A threshold serializes to exactly eight byte values. -/
@[simp] theorem length_berExpThresholdBytes (threshold : BerExpThreshold) :
    (berExpThresholdBytes threshold).length = 8 := by
  simp [berExpThresholdBytes]

/-- Every serialized threshold component is an unsigned byte value. -/
theorem berExpThresholdBytes_lt_256 {threshold : BerExpThreshold} {value : Nat}
    (hvalue : value ∈ berExpThresholdBytes threshold) : value < 2 ^ 8 := by
  rw [berExpThresholdBytes, List.mem_map] at hvalue
  obtain ⟨row, hrow, rfl⟩ := hvalue
  have hrowLength := BitString.length_of_mem_listRows hrow
  simpa only [hrowLength] using BitString.binaryValue_lt_two_pow row

private theorem binaryValue_listRows_lt_iff : ∀ (count width : Nat)
    {left right : List Bool}, left.length = count * width → right.length = count * width →
      (BitString.listRows count width left).map BitString.binaryValue <
          (BitString.listRows count width right).map BitString.binaryValue ↔
        BitString.binaryValue left < BitString.binaryValue right
  | 0, _, left, right, hleft, hright => by
      have hleftNil : left = [] := List.length_eq_zero_iff.mp (by simpa using hleft)
      have hrightNil : right = [] := List.length_eq_zero_iff.mp (by simpa using hright)
      subst left
      subst right
      rfl
  | count + 1, width, left, right, hleft, hright => by
      let leftHead := left.take width
      let rightHead := right.take width
      let leftTail := left.drop width
      let rightTail := right.drop width
      have hwidthLeft : width ≤ left.length := by
        rw [hleft, Nat.succ_mul]
        omega
      have hwidthRight : width ≤ right.length := by
        rw [hright, Nat.succ_mul]
        omega
      have hleftHead : leftHead.length = width := List.length_take_of_le hwidthLeft
      have hrightHead : rightHead.length = width := List.length_take_of_le hwidthRight
      have hleftTail : leftTail.length = count * width := by
        simp only [leftTail, List.length_drop, hleft, Nat.succ_mul]
        omega
      have hrightTail : rightTail.length = count * width := by
        simp only [rightTail, List.length_drop, hright, Nat.succ_mul]
        omega
      have hleftSplit : left = leftHead ++ leftTail :=
        (List.take_append_drop width left).symm
      have hrightSplit : right = rightHead ++ rightTail :=
        (List.take_append_drop width right).symm
      have hleftRows : BitString.listRows (count + 1) width left =
          leftHead :: BitString.listRows count width leftTail := by
        rw [hleftSplit]
        exact BitString.listRows_succ_append count width hleftHead leftTail
      have hrightRows : BitString.listRows (count + 1) width right =
          rightHead :: BitString.listRows count width rightTail := by
        rw [hrightSplit]
        exact BitString.listRows_succ_append count width hrightHead rightTail
      have hleftValue : BitString.binaryValue left =
          BitString.binaryValue leftHead * 2 ^ (count * width) +
            BitString.binaryValue leftTail := by
        rw [hleftSplit, BitString.binaryValue_append, hleftTail]
      have hrightValue : BitString.binaryValue right =
          BitString.binaryValue rightHead * 2 ^ (count * width) +
            BitString.binaryValue rightTail := by
        rw [hrightSplit, BitString.binaryValue_append, hrightTail]
      have hleftBound : BitString.binaryValue leftTail < 2 ^ (count * width) := by
        simpa only [hleftTail] using BitString.binaryValue_lt_two_pow leftTail
      have hrightBound : BitString.binaryValue rightTail < 2 ^ (count * width) := by
        simpa only [hrightTail] using BitString.binaryValue_lt_two_pow rightTail
      rw [hleftRows, hrightRows, List.map_cons, List.map_cons, List.cons_lt_cons_iff,
        binaryValue_listRows_lt_iff count width hleftTail hrightTail,
        hleftValue, hrightValue]
      rcases lt_trichotomy (BitString.binaryValue leftHead)
        (BitString.binaryValue rightHead) with hlt | heq | hgt
      · have hmul := Nat.mul_le_mul_right (2 ^ (count * width)) (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at hmul
        have hvalue : BitString.binaryValue leftHead * 2 ^ (count * width) +
            BitString.binaryValue leftTail <
            BitString.binaryValue rightHead * 2 ^ (count * width) +
              BitString.binaryValue rightTail := by
          omega
        simp [hlt, hlt.ne, hvalue]
      · simp [heq]
      · have hmul := Nat.mul_le_mul_right (2 ^ (count * width)) (Nat.succ_le_of_lt hgt)
        rw [Nat.succ_mul] at hmul
        have hvalue : ¬ (BitString.binaryValue leftHead * 2 ^ (count * width) +
            BitString.binaryValue leftTail <
            BitString.binaryValue rightHead * 2 ^ (count * width) +
              BitString.binaryValue rightTail) := by
          omega
        simp [hgt, hgt.ne, hvalue]

/-- Big-endian byte order on 64-bit words is their ordinary numeric order. -/
theorem berExpThresholdBytes_lt_iff (left right : BerExpThreshold) :
    berExpThresholdBytes left < berExpThresholdBytes right ↔ left.val < right.val := by
  rw [berExpThresholdBytes, berExpThresholdBytes,
    binaryValue_listRows_lt_iff 8 8]
  · simp
  · simpa using BitString.length_binaryWord left.isLt
  · simpa using BitString.length_binaryWord right.isLt

/-- On two 64-bit words, the lazy trace returns the fixed threshold decision. -/
theorem berExpLazyTrace64_accepted (threshold sample : BerExpThreshold) :
    (berExpLazyTrace (berExpThresholdBytes threshold)
      (berExpThresholdBytes sample)).accepted =
        berExpThresholdAccepts threshold sample.val := by
  rw [berExpLazyTrace_accepted (by simp), berExpThresholdAccepts,
    berExpThresholdBytes_lt_iff]

/-- Make sequential eight-bit draws until a byte differs from the corresponding threshold byte. -/
noncomputable def berExpLazyBytes : List Nat → ProbComp BerExpLazyResult
  | [] => pure { accepted := false, bytesRead := 0 }
  | threshold :: thresholds => do
      let sample <- ProbComp.sampleBinaryNat 8
      if sample < threshold then
        pure (BerExpLazyResult.stop true)
      else if threshold < sample then
        pure (BerExpLazyResult.stop false)
      else
        BerExpLazyResult.next <$> berExpLazyBytes thresholds

/-- The source-faithful lazy comparison after Algorithm 14 has produced its threshold. -/
noncomputable def berExpLazyCoin (threshold : BerExpThreshold) : ProbComp BerExpLazyResult :=
  berExpLazyBytes (berExpThresholdBytes threshold)

/-- Sequential early stopping has the trace distribution obtained from a full independent byte
list. The right side is an analysis device; the left side is the program that actually stops. -/
theorem eval_berExpLazyBytes (thresholds : List Nat) :
    ProbComp.eval (berExpLazyBytes thresholds) =
      (ProbComp.eval
        (OracleComp.replicate thresholds.length (ProbComp.sampleBinaryNat 8))).map
          (berExpLazyTrace thresholds) := by
  induction thresholds with
  | nil => simp [berExpLazyBytes, berExpLazyTrace]
  | cons threshold thresholds ih =>
      rw [berExpLazyBytes, OracleComp.replicate_succ]
      simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind, PMF.bind_map,
        Function.comp_def]
      apply PMF.bind_congr_on_support
      intro sample _hsample
      by_cases hlt : sample < threshold
      · simp [berExpLazyTrace, hlt, BerExpLazyResult.stop]
      · by_cases hgt : threshold < sample
        · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.stop]
        · have heq : sample = threshold := Nat.le_antisymm (Nat.not_lt.mp hgt) (Nat.not_lt.mp hlt)
          subst sample
          simp only [lt_self_iff_false, if_false, ih, PMF.map_comp, Function.comp_def]
          congr 1 with result : 1
          rfl

/-- The lazy comparison and the fixed 64-bit comparison have the same decision distribution. -/
theorem eval_berExpLazyCoin_accepted (threshold : BerExpThreshold) :
    (ProbComp.eval (berExpLazyCoin threshold)).map BerExpLazyResult.accepted =
      ProbComp.eval (berExpThresholdCoin threshold) := by
  rw [berExpLazyCoin, eval_berExpLazyBytes, PMF.map_comp]
  have hrepeated := ProbComp.eval_replicate_of_uniformList 8 8
    (ProbComp.sampleBinaryNat 8) BitString.binaryValue (by
      simp only [ProbComp.sampleBinaryNat, ProbComp.eval_map, BitString.eval_sampleList])
  rw [hrepeated]
  simp only [PMF.map_comp, Function.comp_def, berExpThresholdCoin,
    ProbComp.sampleBinaryNat, ProbComp.eval_bind, ProbComp.eval_map,
    BitString.eval_sampleList, ProbComp.eval_pure, PMF.bind_map, PMF.bind_pure_comp]
  apply PMF.map_congr_on_support
  intro tape htape
  have htapeLength : tape.length = 64 :=
    BitString.length_of_mem_support_uniformList htape
  rw [berExpLazyTrace_accepted (by simp), berExpThresholdAccepts]
  apply decide_eq_decide.mpr
  simpa only [berExpThresholdBytes, BitString.binaryValue_binaryWord] using
    (binaryValue_listRows_lt_iff 8 8
      (left := tape) (right := BitString.binaryWord 64 threshold.val)
      (by simpa using htapeLength) (by simpa using BitString.length_binaryWord threshold.isLt))

/-- The lazy comparison accepts with the same exact mass `z / 2^64`. -/
theorem eval_berExpLazyCoin_accepted_true (threshold : BerExpThreshold) :
    ((ProbComp.eval (berExpLazyCoin threshold)).map BerExpLazyResult.accepted) true =
      (threshold.val : ENNReal) / 2 ^ 64 := by
  rw [eval_berExpLazyCoin_accepted, eval_berExpThresholdCoin_true]

/-- Every possible source-faithful lazy comparison reads at least one and at most eight bytes. -/
theorem mem_support_berExpLazyCoin_bytesRead {threshold : BerExpThreshold}
    {result : BerExpLazyResult} (hresult : result ∈ (ProbComp.eval
      (berExpLazyCoin threshold)).support) :
    1 ≤ result.bytesRead ∧ result.bytesRead ≤ 8 := by
  rw [berExpLazyCoin, eval_berExpLazyBytes, PMF.mem_support_map_iff] at hresult
  obtain ⟨samples, hsamples, rfl⟩ := hresult
  have hsamplesLength :=
    ((ProbComp.mem_support_replicate_iff _ _ _).mp hsamples).1
  have hthresholdLength := length_berExpThresholdBytes threshold
  have hthresholdNonempty : berExpThresholdBytes threshold ≠ [] := by
    intro hnil
    rw [hnil] at hthresholdLength
    simp only [List.length_nil] at hthresholdLength
    omega
  have hsamplesNonempty : samples ≠ [] := by
    intro hnil
    rw [hnil] at hsamplesLength
    simp only [List.length_nil] at hsamplesLength
    omega
  obtain ⟨thresholdByte, thresholdBytes, rfl⟩ :=
    List.exists_cons_of_ne_nil hthresholdNonempty
  obtain ⟨sampleByte, sampleBytes, rfl⟩ :=
    List.exists_cons_of_ne_nil hsamplesNonempty
  constructor
  · exact one_le_berExpLazyTrace_bytesRead thresholdByte thresholdBytes sampleByte sampleBytes
  · have hbound := berExpLazyTrace_bytesRead_le
      (thresholdByte :: thresholdBytes) (sampleByte :: sampleBytes)
    omega

private theorem berExpLazyTrace_bytesRead_gt_one {first second : Nat}
    {thresholds samples : List Nat}
    (hlength : samples.length = (first :: second :: thresholds).length) :
    decide (1 < (berExpLazyTrace (first :: second :: thresholds) samples).bytesRead) =
      decide (samples.headD 0 = first) := by
  obtain ⟨sample, samples, rfl⟩ := List.exists_cons_of_length_eq_add_one hlength
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength
  obtain ⟨nextSample, remaining, rfl⟩ := List.exists_cons_of_length_eq_add_one hlength
  by_cases hlt : sample < first
  · simp [berExpLazyTrace, hlt, BerExpLazyResult.stop, hlt.ne]
  · by_cases hgt : first < sample
    · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.stop, hgt.ne]
    · have heq : sample = first := Nat.le_antisymm (Nat.not_lt.mp hgt) (Nat.not_lt.mp hlt)
      subst sample
      have hone := one_le_berExpLazyTrace_bytesRead second thresholds nextSample remaining
      simp [berExpLazyTrace, BerExpLazyResult.next, hone]

private theorem eval_berExpLazyBytes_bytesRead_gt_one (first second : Nat)
    (thresholds : List Nat) (hfirst : first < 2 ^ 8) :
    ((ProbComp.eval (berExpLazyBytes (first :: second :: thresholds))).map
      (fun result => decide (1 < result.bytesRead))) true = (1 : ENNReal) / 2 ^ 8 := by
  rw [eval_berExpLazyBytes, PMF.map_comp]
  apply Eq.trans (congrArg (fun law : PMF Bool => law true) (PMF.map_congr_on_support
    (ProbComp.eval (OracleComp.replicate (first :: second :: thresholds).length
      (ProbComp.sampleBinaryNat 8))) _
    (fun samples => decide (samples.headD 0 = first)) fun samples hsamples => by
      apply berExpLazyTrace_bytesRead_gt_one
      exact ((ProbComp.mem_support_replicate_iff _ _ _).mp hsamples).1))
  rw [show (first :: second :: thresholds).length = (thresholds.length + 1) + 1 by simp,
    OracleComp.replicate_succ]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind, PMF.bind_map,
    Function.comp_def, List.headD_cons, PMF.map_const, PMF.bind_pure_comp,
    Probability.PMF.map_decide_eq_apply_true]
  let firstByte : Fin (2 ^ 8) := ⟨first, hfirst⟩
  rw [ProbComp.eval_sampleBinaryNat,
    show first = firstByte.val from rfl,
    Probability.PMF.map_apply_of_injective _ Fin.val_injective firstByte,
    PMF.uniformOfFintype_apply]
  norm_num

/-- The lazy comparison reads a second byte with exact probability `2^-8`, independently of the
threshold. Equivalently, the first random byte must equal the first threshold byte. -/
theorem eval_berExpLazyCoin_bytesRead_gt_one (threshold : BerExpThreshold) :
    ((ProbComp.eval (berExpLazyCoin threshold)).map
      (fun result => decide (1 < result.bytesRead))) true = (1 : ENNReal) / 2 ^ 8 := by
  let bytes := berExpThresholdBytes threshold
  have hlength : bytes.length = 8 := length_berExpThresholdBytes threshold
  obtain ⟨first, second, rest, hbytes⟩ :
      ∃ first second rest, bytes = first :: second :: rest := by
    cases bytes with
    | nil => simp at hlength
    | cons first tail =>
        cases tail with
        | nil => simp at hlength
        | cons second rest => exact ⟨first, second, rest, rfl⟩
  have hthresholdBytes : berExpThresholdBytes threshold = first :: second :: rest := by
    simpa only [bytes] using hbytes
  have hfirst : first < 2 ^ 8 := by
    apply berExpThresholdBytes_lt_256
    rw [hthresholdBytes]
    simp
  rw [berExpLazyCoin, hthresholdBytes]
  exact eval_berExpLazyBytes_bytesRead_gt_one first second rest hfirst

end Cslib.Crypto.Falcon
