/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-! Checked clients for the named native streaming codecs. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerCodec

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Internal.NativeCompiler

/-- Encoding-equality retyping is a zero-runtime view of the same machine. -/
example {Alpha : Type*} (enc : Alpha ↪ List Bool)
    (compiler : NativeCompiler id enc enc) :
    (compiler.ofInputEq id (fun _ => rfl)).machine = compiler.machine ∧
      (compiler.ofOutputEq (g := id) (fun _ => rfl)).machine = compiler.machine :=
  ⟨rfl, rfl⟩

/-- Pair projections retain the direct frame parsers and expose their exact linear clocks. -/
example :
    (first encUnary encBool).time (3, true) =
      4 * (encPair encUnary encBool (3, true)).length + 8 ∧
    (second encUnary encBool).time (3, true) =
      4 * (encPair encUnary encBool (3, true)).length + 8 :=
  ⟨rfl, rfl⟩

/-- Standard option and sum constructors are direct one-bit prefix transducers. -/
example :
    (optionSome encUnary).outputBits 3 = 4 ∧
      (sumInl encUnary encBool).outputBits 3 = 4 ∧
      (sumInr encUnary encBool).outputBits true = 2 ∧
      (framedValue encUnary).outputBits 3 = 7 := by
  decide

/-- Typed unframing removes only the concrete frame around the encoded value. -/
example : (unframeValue encUnary).outputBits 3 = 3 := by
  decide

/-- Total decoder behavior is explicit on malformed and empty raw words. -/
example :
    List.length [false, true] = 2 ∧
      ([].headD false : Bool) = false ∧
      unframe [true] = [] ∧ dropFrame [true] = [] := by
  decide

/-- The emitted result of every named codec is charged by its exact output coordinate and time. -/
example (input : List Bool) :
    unaryDecoder.outputBits input = input.length ∧
      unaryDecoder.outputBits input ≤ unaryDecoder.time input := by
  constructor
  · simp [NativeCompiler.outputBits, encUnary_apply]
  · exact (unaryDecoder.computes input).length_output_le

/-- Empty-word and unary boundary primitives retain the public finite transducers. -/
example :
    isEmpty.outputBits [] = 1 ∧ isEmpty.outputBits [true] = 1 ∧
      unaryIsZero.outputBits 0 = 1 ∧ unaryPred.outputBits 0 = 0 ∧
      unaryPred.outputBits 3 = 2 := by
  decide

/-- Branch tests use the empty/nonempty encoding, not the one-bit Boolean encoding. -/
example :
    boolToTest.outputBits false = 0 ∧ boolToTest.outputBits true = 1 ∧
      (optionIsSomeBool encUnary).outputBits none = 1 ∧
      (optionIsSomeBool encUnary).outputBits (some 3) = 1 ∧
      (optionIsSomeTest encUnary).outputBits none = 0 ∧
      (optionIsSomeTest encUnary).outputBits (some 3) = 1 ∧
      unaryIsZeroTest.outputBits 0 = 1 ∧ unaryIsZeroTest.outputBits 1 = 0 := by
  decide

/-- The state range is computed from the actual retained encoding. -/
example (state : unaryDecoder.State) :
    unaryDecoder.stateEncoding state < unaryDecoder.stateBound :=
  unaryDecoder.stateEncoding_lt_stateBound state

/-- The retained unary-list decoder preserves the total incomplete-frame convention. -/
example :
    (frames [true, false, true]).map List.length = [1, 0] ∧
      unaryListDecoder.outputBits [true, false, true] = 4 := by
  decide

/-- Bounded reply decoding can use the retained direct list-prefix kernel. -/
example :
    (takeUnary encUnary).time ([2, 1, 3], 2) =
      2 * (3 * (encPair (encList encUnary) encUnary ([2, 1, 3], 2)).length + 2) +
        3 * (2 + 2) + 2 * 1 + 4 ∧
      (takeUnary encUnary).workspace ([2, 1, 3], 2) =
        2 * (2 + 2) + 2 * 1 * (3 * (2 + 2) + 2 * 1 + 3) :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.Machines.Turing.MultiTape.Internal.NativeCompilerCodec
