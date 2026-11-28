/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BitListCodec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.List

/-!
# Named native raw-bit lookup

This definitions-only module retains binary-indexed access to a raw bit word. The concrete
compiler first inserts the standard Boolean-list framing with the shared finite-state codec, then
reuses the retained single-pass binary list lookup. Out-of-range indices return the caller-supplied
fallback.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.bitsGetDNatCompiler`: total binary-indexed lookup in
  a raw bit word.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Turing.MultiTapeTM.Internal

/-- Retained conversion from a raw word to its framed Boolean-list representation. -/
@[expose] noncomputable def frameBits :
    NativeCompiler (id : List Bool → List Bool) encBits (encList encBool) := by
  let convert : NativeCompiler (fun word : List Bool =>
      bitsToBoolListT.run bitsToBoolListT.q₀ word)
      encBits encBits :=
    ofTransducer bitsToBoolListT Universal.eBit fun _ => rfl
  exact ((convert.comp (encodeFrame encBits)).ofOutputEq fun word => by
      simpa only [id_eq, encBits_apply] using (bitsToBoolListT_run word).symm)

/-- Binary-indexed access to a raw bit word, with an explicit out-of-range fallback. The compiler
retains the framing conversion and the complete framed-list scan. -/
@[expose] noncomputable def bitsGetDNatCompiler (fallback : Bool) :
    NativeCompiler (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encNat) encBool := by
  let bits := first encBits encNat
  let index := second encBits encNat
  let listedInput := frameBits.comp bits
  exact (listGetDNatCompiler fallback encBool).comp (listedInput.pair index)

private theorem length_encList_bool (word : List Bool) :
    (encList encBool word).length = 3 * word.length := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    simp only [encList_cons, List.length_append, length_frame, encBool_apply,
      List.length_nil, List.length_cons, ih]
    omega

private noncomputable def unframeBits :
    NativeCompiler (id : List Bool → List Bool) (encList encBool) encBits :=
  ofTransducer listBitsT Fin.valEmbedding fun word => listBitsT_run word

private noncomputable def takeBitsInput :
    NativeCompiler (fun input : List Bool × ℕ => (input.1, input.2))
      (encPair encBits encUnary) (encPair (encList encBool) encUnary) := by
  let word := frameBits.comp (NativeCompiler.first encBits encUnary)
  let count := NativeCompiler.second encBits encUnary
  exact word.pair count

private noncomputable def takeBitsFramed :
    NativeCompiler (fun input : List Bool × ℕ => input.1.take input.2)
      (encPair encBits encUnary) (encList encBool) :=
  (takeUnary encBool).comp takeBitsInput

/-- Canonical retained raw-bit prefix compiler. The executed machine first frames every raw bit,
uses the direct unary encoded-list prefix machine, then removes the frames. -/
noncomputable def takeBits :
    NativeCompiler (fun input : List Bool × ℕ => input.1.take input.2)
      (encPair encBits encUnary) encBits :=
  unframeBits.comp takeBitsFramed

/-- Fully expanded exact clock in the raw-word length, unary count and emitted-prefix length. -/
theorem time_takeBits_expanded (input : List Bool × ℕ) :
    takeBits.time input =
      124 * input.1.length + 21 * input.2 + 24 * (input.1.take input.2).length + 135 := by
  simp only [takeBits, takeBitsFramed, takeBitsInput, frameBits, encodeFrame, unframeBits,
    NativeCompiler.comp, NativeCompiler.pair, first, second,
    ofTransducer, takeUnary, takeDropUnary, NativeCompiler.ofOutputEq, id_eq, length_frame,
    length_encList_bool,
    length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- Fully expanded exact workspace in the raw-word length, unary count and emitted-prefix length. -/
theorem workspace_takeBits_expanded (input : List Bool × ℕ) :
    takeBits.workspace input =
      60 * input.1.length + 13 * input.2 + 15 * (input.1.take input.2).length + 268 := by
  simp only [takeBits, takeBitsFramed, takeBitsInput, frameBits, encodeFrame, unframeBits,
    NativeCompiler.comp, NativeCompiler.pair, first, second,
    ofTransducer, takeUnary, takeDropUnary, NativeCompiler.ofOutputEq, id_eq, length_frame,
    length_encList_bool,
    length_encPair, encBits_apply, encUnary_apply, List.length_replicate]
  omega

/-- A direct linear clock bound in the actual raw-word length and unary count. -/
theorem time_takeBits_le (input : List Bool × ℕ) :
    takeBits.time input ≤ 148 * (input.1.length + input.2 + 1) := by
  rw [time_takeBits_expanded]
  have htake := List.length_take_le input.2 input.1
  omega

/-- A direct linear workspace bound in the actual raw-word length and unary count. -/
theorem workspace_takeBits_le (input : List Bool × ℕ) :
    takeBits.workspace input ≤ 268 * (input.1.length + input.2 + 1) := by
  rw [workspace_takeBits_expanded]
  have htake := List.length_take_le input.2 input.1
  omega


end Turing.MultiTapeTM.Internal.NativeCompiler
