/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.BerExp
public import CslibFrontier.Crypto.Primitives.ByteString
import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.UniformPoint
import Mathlib.Tactic

/-!
# Falcon v1.2 BerExp lazy-byte trace

Falcon v1.2 Algorithm 14 compares a uniform 64-bit word with its threshold one byte at a time,
most significant byte first, and stops at the first mismatch. This module formalizes that
operational boundary after the threshold has already been computed. `berExpLazyCoin` makes one
eight-fair-bit draw for every visited byte, returns the same decision as the fixed 64-bit
experiment in `BerExp.lean`, and records the number of bytes read.

The trace uses the shared `Byte` type and `natToFixedBytesBE` serialization. Its source ledger
records one byte draw, subtraction and comparison per visited byte, exactly eight fair bits per
byte, and no external oracle or handler. These are Algorithm 14 source operations, not
Lean evaluation steps, native instructions, PRNG-buffer refills or a runtime certificate.

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
* `Cslib.Crypto.Falcon.berExpLazyCoin`: the sequential lazy-byte experiment.
* `Cslib.Crypto.Falcon.BerExpLazySourceResources`: the exact per-trace source ledger.

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
* `Cslib.Crypto.Falcon.mem_support_berExpLazyCoin_resources`: every source-facing result charges
  exactly the consumed bytes and zero external resources.

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

/-- Source-level operations and randomness used by one lazy comparison trace.

The subtraction and comparison coordinates describe the source's byte subtraction and sign test,
not the definitional order tests used by `berExpLazyTrace`. -/
structure BerExpLazySourceResources where
  /-- Eight-bit random values requested from the PRNG interface. -/
  byteDrawCount : Nat
  /-- Source byte subtractions `sample - threshold`. -/
  byteSubtractionCount : Nat
  /-- Source sign/equality comparisons of byte differences. -/
  byteComparisonCount : Nat
  /-- Fair random bits underlying the byte draws. -/
  randomBits : Nat
  /-- External oracle queries. -/
  oracleQueries : Nat
  /-- External handler calls. -/
  handlerCalls : Nat
  deriving DecidableEq

/-- The observable result of Algorithm 14's lazy comparison.

`accepted` is the comparison result. `bytesRead` counts eight-bit PRNG outputs consumed by the
comparison itself; it does not count buffer refills or any preceding `BaseSampler` draw. -/
structure BerExpLazyResult where
  /-- Whether the sampled 64-bit word is strictly below the threshold. -/
  accepted : Bool
  /-- The number of consecutive random bytes inspected before stopping. -/
  bytesRead : Nat
  /-- Source-level operations and randomness of this trace. -/
  resources : BerExpLazySourceResources
  deriving DecidableEq

private def BerExpLazyResult.stop (accepted : Bool) : BerExpLazyResult :=
  { accepted, bytesRead := 1,
    resources := ⟨1, 1, 1, 8, 0, 0⟩ }

private def BerExpLazyResult.next (result : BerExpLazyResult) : BerExpLazyResult :=
  { result with
    bytesRead := result.bytesRead + 1
    resources :=
      { byteDrawCount := result.resources.byteDrawCount + 1
        byteSubtractionCount := result.resources.byteSubtractionCount + 1
        byteComparisonCount := result.resources.byteComparisonCount + 1
        randomBits := result.resources.randomBits + 8
        oracleQueries := result.resources.oracleQueries
        handlerCalls := result.resources.handlerCalls } }

/-- Compare byte values from left to right, stopping at the first mismatch.

The source-faithful use has two lists of eight values below `256`. The definition is total on
arbitrary lists: exhaustion before a mismatch rejects, and every matched pair is counted. -/
@[expose] def berExpLazyTrace : List Byte → List Byte → BerExpLazyResult
  | threshold :: thresholds, sample :: samples =>
      if sample < threshold then
        BerExpLazyResult.stop true
      else if threshold < sample then
        BerExpLazyResult.stop false
      else
        (berExpLazyTrace thresholds samples).next
  | _, _ => { accepted := false, bytesRead := 0, resources := ⟨0, 0, 0, 0, 0, 0⟩ }

/-- On lists of equal length, the lazy trace accepts exactly at strict lexicographic comparison. -/
theorem berExpLazyTrace_accepted {thresholds samples : List Byte}
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
theorem berExpLazyTrace_bytesRead_le (thresholds samples : List Byte) :
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

private theorem one_le_berExpLazyTrace_bytesRead (threshold : Byte) (thresholds : List Byte)
    (sample : Byte) (samples : List Byte) :
    1 ≤ (berExpLazyTrace (threshold :: thresholds) (sample :: samples)).bytesRead := by
  by_cases hlt : sample < threshold
  · simp [berExpLazyTrace, hlt, BerExpLazyResult.stop]
  · by_cases hgt : threshold < sample
    · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.stop]
    · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.next]

/-- Every deterministic trace ledger charges exactly the byte pairs it consumed. -/
private theorem berExpLazyTrace_resources (thresholds samples : List Byte) :
    let result := berExpLazyTrace thresholds samples
    result.resources.byteDrawCount = result.bytesRead ∧
      result.resources.byteSubtractionCount = result.bytesRead ∧
      result.resources.byteComparisonCount = result.bytesRead ∧
      result.resources.randomBits = 8 * result.bytesRead ∧
      result.resources.oracleQueries = 0 ∧
      result.resources.handlerCalls = 0 := by
  induction thresholds generalizing samples with
  | nil => simp [berExpLazyTrace]
  | cons threshold thresholds ih =>
      cases samples with
      | nil => simp [berExpLazyTrace]
      | cons sample samples =>
          by_cases hlt : sample < threshold
          · simp [berExpLazyTrace, hlt, BerExpLazyResult.stop]
          · by_cases hgt : threshold < sample
            · simp [berExpLazyTrace, hlt, hgt, BerExpLazyResult.stop]
            · have hresources := ih samples
              simp only [berExpLazyTrace, hlt, hgt, if_false, BerExpLazyResult.next]
              omega

/-- The shared eight-byte big-endian representation of a 64-bit threshold. -/
private def berExpThresholdBytes (threshold : BerExpThreshold) : List Byte :=
  (natToFixedBytesBE 8 threshold.val).toList

@[simp] private theorem length_berExpThresholdBytes (threshold : BerExpThreshold) :
    (berExpThresholdBytes threshold).length = 8 := by
  simp [berExpThresholdBytes]

private theorem bytesToBitsBE_berExpThresholdBytes (threshold : BerExpThreshold) :
    bytesToBitsBE (berExpThresholdBytes threshold) =
      BitString.binaryWord 64 threshold.val := by
  apply BitString.binaryValue_injective_of_length_eq
  · simp [berExpThresholdBytes]
  · have hvalue := threshold.isLt
    norm_num [berExpThresholdBytes, FixedBytes.toList, natToFixedBytesBE,
      List.ofFn_succ, bytesToBitsBE, byteBitsBE, BitString.binaryValue_append] at hvalue ⊢
    omega

private theorem berExpThresholdBytes_lt_iff (left right : BerExpThreshold) :
    berExpThresholdBytes left < berExpThresholdBytes right ↔ left.val < right.val := by
  have hlength : (berExpThresholdBytes left).length =
      (berExpThresholdBytes right).length := by simp
  constructor
  · intro hbytes
    have hbits := (bytesToBitsBE_lt_iff_lt hlength).mpr hbytes
    rw [bytesToBitsBE_berExpThresholdBytes, bytesToBitsBE_berExpThresholdBytes] at hbits
    have hvalues := (BitString.binaryValue_lt_iff_lt (by simp)).mpr hbits
    simpa using hvalues
  · intro hvalues
    apply (bytesToBitsBE_lt_iff_lt hlength).mp
    rw [bytesToBitsBE_berExpThresholdBytes, bytesToBitsBE_berExpThresholdBytes]
    apply (BitString.binaryValue_lt_iff_lt (by simp)).mp
    simpa using hvalues

/-- On two 64-bit words, the lazy trace returns the fixed threshold decision. -/
theorem berExpLazyTrace64_accepted (threshold sample : BerExpThreshold) :
    (berExpLazyTrace (natToFixedBytesBE 8 threshold.val).toList
      (natToFixedBytesBE 8 sample.val).toList).accepted =
        berExpThresholdAccepts threshold sample.val := by
  change (berExpLazyTrace (berExpThresholdBytes threshold)
    (berExpThresholdBytes sample)).accepted = _
  rw [berExpLazyTrace_accepted (by simp), berExpThresholdAccepts,
    berExpThresholdBytes_lt_iff]

/-- Reduce a natural value to the shared unsigned-byte type. -/
private def berExpByteOfNat (value : Nat) : Byte :=
  ⟨value % 256, Nat.mod_lt _ (by decide)⟩

/-- One byte produced by exactly eight fair-bit draws. -/
private noncomputable def berExpLazyByte : ProbComp Byte :=
  berExpByteOfNat <$> ProbComp.sampleBinaryNat 8

private theorem eval_berExpLazyByte :
    ProbComp.eval berExpLazyByte = PMF.uniformOfFintype Byte := by
  rw [berExpLazyByte, ProbComp.eval_map, ProbComp.eval_sampleBinaryNat, PMF.map_comp]
  convert PMF.map_id (PMF.uniformOfFintype (Fin (2 ^ 8))) using 1
  funext value
  apply Fin.ext
  simp [berExpByteOfNat, Nat.mod_eq_of_lt value.isLt]

/-- Make sequential eight-bit draws until a byte differs from the corresponding threshold byte. -/
private noncomputable def berExpLazyBytes : List Byte → ProbComp BerExpLazyResult
  | [] => pure { accepted := false, bytesRead := 0, resources := ⟨0, 0, 0, 0, 0, 0⟩ }
  | threshold :: thresholds => do
      let sample <- berExpLazyByte
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
private theorem eval_berExpLazyBytes (thresholds : List Byte) :
    ProbComp.eval (berExpLazyBytes thresholds) =
      (ProbComp.eval
        (OracleComp.replicate thresholds.length berExpLazyByte)).map
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
        · have heq : sample = threshold := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
          subst sample
          simp only [lt_self_iff_false, if_false, ih, PMF.map_comp, Function.comp_def]
          congr 1 with result : 1
          rfl

private theorem bytesToBitsBE_map_berExpByteOfNat_listRows : ∀ (count : Nat)
    {bits : List Bool}, bits.length = count * 8 →
      bytesToBitsBE ((BitString.listRows count 8 bits).map
        (fun row => berExpByteOfNat (BitString.binaryValue row))) = bits
  | 0, bits, hlength => by
      have hbits : bits = [] := List.length_eq_zero_iff.mp (by simpa using hlength)
      subst bits
      simp [bytesToBitsBE]
  | count + 1, bits, hlength => by
      let head := bits.take 8
      let tail := bits.drop 8
      have hwidth : 8 ≤ bits.length := by
        rw [hlength, Nat.succ_mul]
        omega
      have hhead : head.length = 8 := List.length_take_of_le hwidth
      have htail : tail.length = count * 8 := by
        simp only [tail, List.length_drop, hlength, Nat.succ_mul]
        omega
      have hsplit : bits = head ++ tail := (List.take_append_drop 8 bits).symm
      have hbyte : berExpByteOfNat (BitString.binaryValue head) = byteOfBitsBE head := by
        apply Fin.ext
        simp [berExpByteOfNat, byteOfBitsBE, List.take_of_length_le hhead.le,
          Nat.mod_eq_of_lt (by simpa only [hhead] using BitString.binaryValue_lt_two_pow head)]
      rw [hsplit, BitString.listRows_succ_append count 8 hhead tail]
      simp only [List.map_cons, bytesToBitsBE, hbyte]
      rw [byteBitsBE_byteOfBitsBE head hhead,
        bytesToBitsBE_map_berExpByteOfNat_listRows count htail]

/-- The lazy comparison and the fixed 64-bit comparison have the same decision distribution. -/
theorem eval_berExpLazyCoin_accepted (threshold : BerExpThreshold) :
    (ProbComp.eval (berExpLazyCoin threshold)).map BerExpLazyResult.accepted =
      ProbComp.eval (berExpThresholdCoin threshold) := by
  rw [berExpLazyCoin, eval_berExpLazyBytes, PMF.map_comp]
  have hrepeated := ProbComp.eval_replicate_of_uniformList 8 8
    berExpLazyByte (fun bits => berExpByteOfNat (BitString.binaryValue bits)) (by
      simp only [berExpLazyByte, ProbComp.sampleBinaryNat, ProbComp.eval_map,
        BitString.eval_sampleList, PMF.map_comp, Function.comp_def])
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
  calc
    (BitString.listRows 8 8 tape).map
          (fun bits => berExpByteOfNat (BitString.binaryValue bits)) <
        berExpThresholdBytes threshold ↔
        bytesToBitsBE ((BitString.listRows 8 8 tape).map
          (fun bits => berExpByteOfNat (BitString.binaryValue bits))) <
            bytesToBitsBE (berExpThresholdBytes threshold) :=
      (bytesToBitsBE_lt_iff_lt (by simp)).symm
    _ ↔ tape < BitString.binaryWord 64 threshold.val := by
      rw [bytesToBitsBE_map_berExpByteOfNat_listRows 8 (by simpa using htapeLength),
        bytesToBitsBE_berExpThresholdBytes]
    _ ↔ BitString.binaryValue tape <
        BitString.binaryValue (BitString.binaryWord 64 threshold.val) :=
      (BitString.binaryValue_lt_iff_lt (by
        simpa using htapeLength.trans (BitString.length_binaryWord threshold.isLt).symm)).symm
    _ ↔ BitString.binaryValue tape < threshold.val := by
      rw [BitString.binaryValue_binaryWord]

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

/-- Every result of the source-facing experiment records its exact source-level byte operations,
fair-bit consumption and zero external resources. -/
theorem mem_support_berExpLazyCoin_resources {threshold : BerExpThreshold}
    {result : BerExpLazyResult} (hresult : result ∈ (ProbComp.eval
      (berExpLazyCoin threshold)).support) :
    result.resources.byteDrawCount = result.bytesRead ∧
      result.resources.byteSubtractionCount = result.bytesRead ∧
      result.resources.byteComparisonCount = result.bytesRead ∧
      result.resources.randomBits = 8 * result.bytesRead ∧
      result.resources.oracleQueries = 0 ∧
      result.resources.handlerCalls = 0 := by
  rw [berExpLazyCoin, eval_berExpLazyBytes, PMF.mem_support_map_iff] at hresult
  obtain ⟨samples, _hsamples, rfl⟩ := hresult
  exact berExpLazyTrace_resources (berExpThresholdBytes threshold) samples

private theorem berExpLazyTrace_bytesRead_gt_one {first second : Byte}
    {thresholds samples : List Byte}
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
    · have heq : sample = first := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      subst sample
      have hone := one_le_berExpLazyTrace_bytesRead second thresholds nextSample remaining
      simp [berExpLazyTrace, BerExpLazyResult.next, hone]

private theorem eval_berExpLazyBytes_bytesRead_gt_one (first second : Byte)
    (thresholds : List Byte) :
    ((ProbComp.eval (berExpLazyBytes (first :: second :: thresholds))).map
      (fun result => decide (1 < result.bytesRead))) true = (1 : ENNReal) / 2 ^ 8 := by
  rw [eval_berExpLazyBytes, PMF.map_comp]
  apply Eq.trans (congrArg (fun law : PMF Bool => law true) (PMF.map_congr_on_support
    (ProbComp.eval (OracleComp.replicate (first :: second :: thresholds).length
      berExpLazyByte)) _
    (fun samples => decide (samples.headD 0 = first)) fun samples hsamples => by
      apply berExpLazyTrace_bytesRead_gt_one
      exact ((ProbComp.mem_support_replicate_iff _ _ _).mp hsamples).1))
  rw [show (first :: second :: thresholds).length = (thresholds.length + 1) + 1 by simp,
    OracleComp.replicate_succ]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, PMF.map_bind, PMF.bind_map,
    Function.comp_def, List.headD_cons, PMF.map_const, PMF.bind_pure_comp,
    Probability.PMF.map_decide_eq_apply_true]
  rw [eval_berExpLazyByte, PMF.uniformOfFintype_apply]
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
  rw [berExpLazyCoin, hthresholdBytes]
  exact eval_berExpLazyBytes_bytesRead_gt_one first second rest

end Cslib.Crypto.Falcon
