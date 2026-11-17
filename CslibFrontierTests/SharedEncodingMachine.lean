/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (shared encoding machine regression tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Foundations.Data.BitString.List.PrefixFree
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.FirstMatch
import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partialize

/-! Ordinary-import clients of shared encodings and native machine certificates. -/

namespace CslibFrontierTests.SharedEncodingMachine

open Turing.MultiTapeTM

/-- Mixed fields exercise framing, empty options and list payloads. -/
structure Packet where
  /-- A one-bit tag. -/
  tag : Bool
  /-- Optional unframed payload. -/
  payload : Option (List Bool)

enc_structure encPacket : Packet where tag : encBool, payload : (encOption encBits)

-- The generated encoding retains the former field-tuple word, through the shared product.
example (p : Packet) : encPacket p =
    Cslib.Encoding.encProd Cslib.Encoding.encBool
      (Cslib.Encoding.encOption Cslib.Encoding.encBits) (p.tag, p.payload) := rfl

example : encPacket ⟨false, some []⟩ = [true, false, false, true] := rfl

example (p : Packet) : (encBool p.tag).length ≤ (encPacket p).length :=
  encPacket_tag_length_le p

-- Shared encodings accept the machine rules without transports or changed resource bounds.
example : ComputableInTimeAndSpace (· + 1) Cslib.Encoding.encNat Cslib.Encoding.encNat
    (fun n => 2 * (Cslib.Encoding.encNat n).length + 3) (fun _ => 0) :=
  computableInTimeAndSpace_succ

example (n : ℕ) : encNat n = n.bits := encNat_apply n

-- The fixed-width client keeps its previous literal range/testBit layout.
example (K : ℕ) (i : Fin K) : Cslib.BitString.finIdxBits K i =
    (List.range (Nat.clog 2 K)).map i.val.testBit := rfl

-- Absence, a present empty payload, and a present absent option remain distinct.
example : encOption encBits none = [false] ∧ encOption encBits (some []) = [true] ∧
    encOption (encOption encBits) (some none) = [true, false] := ⟨rfl, rfl, rfl⟩
example : encList (encOption encBits) [none, some []] =
    [true, false, false, true, true, false] := rfl
example : encSilentOption encBits none = [] ∧ encHaltOption encBits none = [] := ⟨rfl, rfl⟩
example : encPacket ⟨false, none⟩ = [true, false, false, false] := rfl
example : ComputableInDegree (Option.isSome : Option (List Bool) → Bool)
    (encOption encBits) encBool 1 0 := ComputableInDegree.isSome encBits
example : ComputableInDegree (id : Option (List Bool) → Option (List Bool))
    (encSilentOption encBits) (encOption encBits) 1 1 :=
  ComputableInDegree.optionFromHalt encBits
example : ComputableInDegree (id : Option (List Bool) → Option (List Bool))
    (encOption encBits) (encSilentOption encBits) 1 1 :=
  ComputableInDegree.optionTranslate encBits

-- The lookup keeps silent callbacks and charges conversion at its public tagged result boundary.
example : (Internal.NativeCompiler.firstMatchCompiler encBool encBits).machine =
    (Internal.NativeCompiler.optionFromHalt encBits).machine.comp
      (Internal.NativeCompiler.firstMatchHaltCompiler encBool encBits).machine true := rfl
example : Internal.NativeCompiler.firstMatch ([(false, []), (true, [true])], false) = some [] := rfl
example : Internal.NativeCompiler.firstMatch ([(false, [])], true) = none := rfl

example (o : Option (List Bool)) : encSilentOption encBits o = o.elim [] (true :: ·) := rfl

example : (Internal.NativeCompiler.optionIsSomeBool encBits).machine.ComputesTidilyInTimeAndSpace
    [false] [false] ((Internal.NativeCompiler.optionIsSomeBool encBits).time none)
    ((Internal.NativeCompiler.optionIsSomeBool encBits).workspace none) := by
  exact (Internal.NativeCompiler.optionIsSomeBool encBits).computes none

-- Generic sigma and sum reuse preserves these domain-specific words exactly.
example {σ : Cslib.Circuits.Signature} (encOp : σ.Op ↪ List Bool) (m : ℕ)
    (c : Σ n, Cslib.Circuits.Circuit σ n m) :
    Cslib.Circuits.Circuit.encCircuit encOp m c =
      encPair encUnary (Cslib.Circuits.Circuit.encCode encOp) (c.1, c.2.code) := rfl
example : encPartial none = [true] ∧ encPartial (some []) = [false] := ⟨rfl, rfl⟩

end CslibFrontierTests.SharedEncodingMachine
