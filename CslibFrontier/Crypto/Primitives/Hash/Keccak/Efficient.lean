/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Hash.Keccak
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Crypto.Primitives.Hash.Keccak.Circuit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Uniform polynomial-time certificates for SHA3-512 and SHAKE256

This module gives uniform multitape-Turing-machine certificates for the byte-oriented FIPS 202
functions in `CslibFrontier.Crypto.Primitives.Hash.Keccak`. A byte is represented by exactly eight
bits in the same least-significant-bit-first order as the executable specification. Byte strings
use the ordinary framed list encoding, and an XOF request pairs that string with a unary output
length. The unary length charges every requested output byte.

The fixed Keccak-p[1600, 24] transformation is realized by the direct retained Boolean circuit in
`CslibFrontier.Crypto.Primitives.Hash.Keccak.Circuit`: the uniform certificate below is derived
from that construction, not from a finite-function table. Its named compiler separately retains
exact time, workspace, input, output, and complete generated transition-table size. The surrounding
variable-length sponge proofs in this module are asymptotic certificates; they do not claim a
concrete bound for the whole sponge.

## Main definitions

* `Cslib.Crypto.Keccak.encByteLE`: the exact eight-bit, least-significant-bit-first byte encoding.
* `Cslib.Crypto.Keccak.encByteStringLE`: framed lists of encoded bytes.
* `Cslib.Crypto.Keccak.encByteXofInput`: a byte string followed by a unary output-byte count.
* `Cslib.Crypto.Keccak.encSpongeView`: framed rate bits followed by framed capacity bits.

## Main results

* `Cslib.Crypto.Keccak.computableInPolyTime_byteSponge`: every fixed lane-aligned layout and
  suffix has a uniform polynomial-time byte-sponge implementation.
* `Cslib.Crypto.Keccak.computableInPolyTime_sha3512`: uniform polynomial time for SHA3-512.
* `Cslib.Crypto.Keccak.computableInPolyTime_shake256`: uniform polynomial time for SHAKE256,
  including its requested output length.
-/

public section

namespace Cslib.Crypto.Keccak

open Cslib Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- A byte as its eight FIPS 202 bits, least significant bit first. -/
@[expose] def encByteLE : Fin 256 ↪ List Bool where
  toFun := byteBitsLE
  inj' := by
    intro a b h
    have := congrArg bitsToByteLE h
    simpa using this

/-- A byte string as an ordinary framed list of eight-bit little-endian bytes. -/
abbrev encByteStringLE : List (Fin 256) ↪ List Bool := encList encByteLE

/-- The input to a byte XOF: framed little-endian bytes, followed by a unary output-byte count. -/
abbrev encByteXofInput : (List (Fin 256) × ℕ) ↪ List Bool :=
  encPair encByteStringLE encUnary

/-- A split Keccak state as a framed pair: the `64 * rateLanes` rate bits first, then the
`64 * capacityLanes` capacity bits. -/
abbrev encSpongeView (layout : SpongeLayout) : SpongeView layout ↪ List Bool :=
  encPair (encBitString (64 * layout.rateLanes))
    (encBitString (64 * layout.capacityLanes))

private theorem computableInPolyTime_bytesToBitsLE :
    ComputableInPolyTime bytesToBitsLE encByteStringLE encBits := by
  apply flatMapToBitsWithInput (id' (encIn := encByteStringLE))
  exact (snd encByteStringLE encByteLE).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_pad10star1 (rate : ℕ) :
    ComputableInPolyTime (pad10star1 rate) encUnary encBits := by
  fun_prop [pad10star1]

private theorem computableInPolyTime_toBlocks (rate : ℕ) :
    ComputableInPolyTime (BitString.toBlocks rate) encBits
      (encList (encBitString rate)) := by
  have hraw : ComputableInPolyTime
      (fun p : (List Bool × ℕ) =>
        (List.range rate).map fun i => p.1.getD (p.2 * rate + i) false)
      (encPair encBits encUnary) encBits :=
    mapToBitsWithInput (range.comp (const rate)) (by fun_prop)
  have hblock : ComputableInPolyTime
      (fun p : (List Bool × ℕ) =>
        fun i : Fin rate => p.1.getD (p.2 * rate + i) false)
      (encPair encBits encUnary) (encBitString rate) :=
    hraw.of_enc_eq fun _ => by simp [encBitString, List.map_range_eq_ofFn]
  exact (mapWithInput
    (f := fun bits b => fun i : Fin rate => bits.getD (b * rate + i) false)
    (list := fun bits : List Bool => List.range (bits.length / rate))
    (range.comp ((unary_div_const rate).comp length_bits)) hblock).of_enc_eq fun bits => by
      rw [BitString.toBlocks_eq_map_range]

private theorem computableInPolyTime_keccakP1600Bits : ComputableInPolyTime
    (fun bits : BitString 1600 => stateBits (keccakP1600Rounds24 (stateOfBits bits)))
    (encBitString 1600) (encBitString 1600) :=
  (Cslib.Circuits.Boolean.computableInPolyTime_evalFixedCircuit
    keccakP1600Circuit).of_enc_eq fun bits =>
      congrArg (encBitString 1600) (eval_keccakP1600Circuit bits).symm

/-- Keccak-p[1600, 24] is polynomial-time on every fixed rate/capacity split, by encoding the
split as the exact flat state consumed by the retained circuit and converting the result back. -/
theorem computableInPolyTime_keccakP1600Rounds24View (layout : SpongeLayout) :
    ComputableInPolyTime (keccakP1600Rounds24View layout)
      (encSpongeView layout) (encSpongeView layout) := by
  have hflatten : ComputableInPolyTime
      (fun state : SpongeView layout => stateBits (ofSpongeView layout state))
      (encSpongeView layout) (encBitString 1600) :=
    ComputableInPolyTime.of_finite _
  have hunflatten : ComputableInPolyTime
      (fun bits : BitString 1600 => toSpongeView layout (stateOfBits bits))
      (encBitString 1600) (encSpongeView layout) :=
    ComputableInPolyTime.of_finite _
  exact (hunflatten.comp (computableInPolyTime_keccakP1600Bits.comp hflatten)).of_enc_eq
    fun state => by
    simp only [Function.comp_apply, keccakP1600Rounds24View, stateOfBits_stateBits]

private theorem computableInPolyTime_absorb (layout : SpongeLayout) :
    ComputableInPolyTime
      (Sponge.absorb (keccakP1600Rounds24View layout))
      (encList (encBitString (64 * layout.rateLanes))) (encSpongeView layout) := by
  have hpreprocess : ComputableInPolyTime
      (fun p : SpongeView layout × BitString (64 * layout.rateLanes) =>
        (p.1.1 + p.2, p.1.2))
      (encPair (encSpongeView layout) (encBitString (64 * layout.rateLanes)))
      (encSpongeView layout) := by
    let encStep := encPair (encSpongeView layout)
      (encBitString (64 * layout.rateLanes))
    have hstate := fst (encSpongeView layout) (encBitString (64 * layout.rateLanes))
    have hrateList : ComputableInPolyTime
        (fun p : SpongeView layout × BitString (64 * layout.rateLanes) => List.ofFn p.1.1)
        encStep encBits := hstate.fst'.of_enc_eq fun _ => rfl
    have hblockList : ComputableInPolyTime
        (fun p : SpongeView layout × BitString (64 * layout.rateLanes) => List.ofFn p.2)
        encStep encBits :=
      (snd (encSpongeView layout) (encBitString (64 * layout.rateLanes))).of_enc_eq fun _ => rfl
    have hsumList := bitsZipWithInput Bool.xor hrateList hblockList
    have hsum : ComputableInPolyTime
        (fun p : SpongeView layout × BitString (64 * layout.rateLanes) => p.1.1 + p.2)
        encStep (encBitString (64 * layout.rateLanes)) :=
      hsumList.of_enc_eq fun p => Cslib.BitString.ofFn_add p.1.1 p.2
    exact hsum.prod hstate.snd'
  have hstep : ComputableInPolyTime
      (fun p : SpongeView layout × BitString (64 * layout.rateLanes) =>
        Sponge.absorbStep (keccakP1600Rounds24View layout) p.1 p.2)
      (encPair (encSpongeView layout) (encBitString (64 * layout.rateLanes)))
      (encSpongeView layout) := by
    unfold Sponge.absorbStep
    exact (computableInPolyTime_keccakP1600Rounds24View layout).comp hpreprocess
  exact Turing.MultiTapeTM.ComputableInPolyTime.foldl_of_bounded_growth
    (encA := encBitString (64 * layout.rateLanes))
    (encL := encList (encBitString (64 * layout.rateLanes)))
    (encB := encSpongeView layout)
    (step := Sponge.absorbStep (keccakP1600Rounds24View layout))
    (id' (encIn := encList (encBitString (64 * layout.rateLanes))))
    (const (0 : SpongeView layout))
    hstep
    (growth := 0)
    fun _ _ => by simp [encSpongeView]

private theorem computableInPolyTime_iteratePermutation (layout : SpongeLayout) :
    ComputableInPolyTime
      (fun p : SpongeView layout × ℕ =>
        (keccakP1600Rounds24View layout)^[p.2] p.1)
      (encPair (encSpongeView layout) encUnary) (encSpongeView layout) := by
  exact Turing.MultiTapeTM.ComputableInPolyTime.iterate_of_bounded_growth
    (snd (encSpongeView layout) encUnary)
    (fst (encSpongeView layout) encUnary)
    (computableInPolyTime_keccakP1600Rounds24View layout)
    (growth := 0)
    fun _ => by simp [encSpongeView]

private theorem squeeze_eq_map_range {R C O : Type*} (P : R × C → R × C)
    (out : R × C → O) (count : ℕ) (state : R × C) :
    Sponge.squeeze P out count state =
      (List.range count).map fun i => out (P^[i] state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [Sponge.squeeze, ih]
    refine List.ext_getElem (by simp) fun i _ _ => ?_
    cases i <;> simp [← Function.iterate_succ_apply, Function.iterate_succ_apply']

private theorem computableInPolyTime_squeezeRates (layout : SpongeLayout) :
    ComputableInPolyTime
      (fun p : SpongeView layout × ℕ =>
        Sponge.squeeze (keccakP1600Rounds24View layout) Prod.fst p.2 p.1)
      (encPair (encSpongeView layout) encUnary)
      (encList (encBitString (64 * layout.rateLanes))) := by
  have hiterInput : ComputableInPolyTime
      (fun p : (SpongeView layout × ℕ) × ℕ => (p.1.1, p.2))
      (encPair (encPair (encSpongeView layout) encUnary) encUnary)
      (encPair (encSpongeView layout) encUnary) :=
    ((fst (encSpongeView layout) encUnary).comp
      (fst (encPair (encSpongeView layout) encUnary) encUnary)).prod
    (snd (encPair (encSpongeView layout) encUnary) encUnary)
  have hbody : ComputableInPolyTime
      (fun p : (SpongeView layout × ℕ) × ℕ =>
        ((keccakP1600Rounds24View layout)^[p.2] p.1.1).1)
      (encPair (encPair (encSpongeView layout) encUnary) encUnary)
      (encBitString (64 * layout.rateLanes)) :=
    (fst (encBitString (64 * layout.rateLanes))
      (encBitString (64 * layout.capacityLanes))).comp
      ((computableInPolyTime_iteratePermutation layout).comp hiterInput)
  exact (mapWithInput
    (f := fun p : SpongeView layout × ℕ => fun i =>
      ((keccakP1600Rounds24View layout)^[i] p.1).1)
    (list := fun p : SpongeView layout × ℕ => List.range p.2)
    (range.comp (snd (encSpongeView layout) encUnary)) hbody).of_enc_eq fun _ => by
      rw [squeeze_eq_map_range]

private theorem computableInPolyTime_hashBlocks (layout : SpongeLayout) :
    ComputableInPolyTime
      (fun p : List (BitString (64 * layout.rateLanes)) × ℕ =>
        Sponge.hashBlocks (keccakP1600Rounds24View layout) Prod.fst p.2 p.1)
      (encPair (encList (encBitString (64 * layout.rateLanes))) encUnary)
      (encList (encBitString (64 * layout.rateLanes))) := by
  exact (computableInPolyTime_squeezeRates layout).comp
    (((computableInPolyTime_absorb layout).comp
      (fst (encList (encBitString (64 * layout.rateLanes))) encUnary)).prod
    (snd (encList (encBitString (64 * layout.rateLanes))) encUnary))

private theorem computableInPolyTime_squeezeBytesFor (layout : SpongeLayout) :
    ComputableInPolyTime
      (fun p : List (BitString (64 * layout.rateLanes)) × ℕ =>
        squeezeBytesFor layout p.1 p.2)
      (encPair (encList (encBitString (64 * layout.rateLanes))) encUnary)
      encByteStringLE := by
  unfold squeezeBytesFor
  have hbody : ComputableInPolyTime
      (fun p : (List (BitString (64 * layout.rateLanes)) × ℕ) ×
        BitString (64 * layout.rateLanes) => rateBytesFor layout p.2)
      (encPair
        (encPair (encList (encBitString (64 * layout.rateLanes))) encUnary)
        (encBitString (64 * layout.rateLanes))) encByteStringLE :=
    (ComputableInPolyTime.of_finite (rateBytesFor layout)).comp
      (snd (encPair (encList (encBitString (64 * layout.rateLanes))) encUnary)
        (encBitString (64 * layout.rateLanes)))
  exact flatMapWithInput (computableInPolyTime_hashBlocks layout) hbody

/-- For every fixed Keccak-p[1600] lane split and suffix, the executable byte sponge is uniformly
polynomial-time in the framed input bytes and the unary requested output length. -/
@[fun_prop] theorem computableInPolyTime_byteSponge (layout : SpongeLayout)
    (suffix : List Bool) :
    ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => byteSponge layout suffix p.1 p.2)
      encByteXofInput encByteStringLE := by
  let rate := 64 * layout.rateLanes
  let rateBytes := 8 * layout.rateLanes
  have hsuffixed : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => bytesToBitsLE p.1 ++ suffix)
      encByteXofInput encBits :=
    bitsAppend (computableInPolyTime_bytesToBitsLE.comp (fst encByteStringLE encUnary))
      (const suffix)
  have hpadded : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ =>
        let suffixed := bytesToBitsLE p.1 ++ suffix
        suffixed ++ pad10star1 rate suffixed.length)
      encByteXofInput encBits :=
    bitsAppend hsuffixed
      ((computableInPolyTime_pad10star1 rate).comp (length_bits.comp hsuffixed))
  have hblocks : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ =>
        let suffixed := bytesToBitsLE p.1 ++ suffix
        BitString.toBlocks rate (suffixed ++ pad10star1 rate suffixed.length))
      encByteXofInput (encList (encBitString rate)) :=
    (computableInPolyTime_toBlocks rate).comp hpadded
  have houtput : ComputableInPolyTime (fun p : List (Fin 256) × ℕ => p.2)
      encByteXofInput encUnary := snd encByteStringLE encUnary
  have hblockCount : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ => p.2 ⌈/⌉ rateBytes)
      encByteXofInput encUnary :=
    ((unary_div_const rateBytes).comp
      (unary_sub' (unary_add' houtput (const rateBytes)) (const 1))).of_enc_eq fun _ => by
      congr 1
  have hsqueezed : ComputableInPolyTime
      (fun p : List (Fin 256) × ℕ =>
        let suffixed := bytesToBitsLE p.1 ++ suffix
        let padded := suffixed ++ pad10star1 rate suffixed.length
        squeezeBytesFor layout (BitString.toBlocks rate padded) (p.2 ⌈/⌉ rateBytes))
      encByteXofInput encByteStringLE :=
    (computableInPolyTime_squeezeBytesFor layout).comp (hblocks.prod hblockCount)
  simpa only [byteSponge, bitSponge, rate, rateBytes] using
    Turing.MultiTapeTM.ComputableInPolyTime.listTakeWithInput hsqueezed houtput

/-- SHA3-512 is uniformly polynomial-time in its framed little-endian input bytes. -/
@[fun_prop] theorem computableInPolyTime_sha3512 :
    ComputableInPolyTime sha3512 encByteStringLE encByteStringLE := by
  change ComputableInPolyTime
    (fun input => byteSponge sha3512Layout [false, true] input 64)
    encByteStringLE encByteStringLE
  simpa only [Function.comp_def] using
    (computableInPolyTime_byteSponge sha3512Layout [false, true]).comp
      ((id' (encIn := encByteStringLE)).prod (const 64))

/-- SHAKE256 is uniformly polynomial-time when the requested number of output bytes is unary. -/
@[fun_prop] theorem computableInPolyTime_shake256 :
    ComputableInPolyTime (fun p : List (Fin 256) × ℕ => shake256 p.1 p.2)
      encByteXofInput encByteStringLE := by
  simpa only [shake256, byteXof] using
    computableInPolyTime_byteSponge shake256Layout [true, true, true, true]

end Cslib.Crypto.Keccak
