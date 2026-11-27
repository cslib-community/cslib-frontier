/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-! # Checked named native compiler construction -/

set_option linter.privateModule false

public section

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal Turing.MultiTapeTM.Universal

namespace CslibFrontierTests.Internal.NativeCompilerWitness

/-- A nonconstant direct compiler pipeline: preserve the input bit and attach a true tag. -/
private def tagged :
    NativeCompiler (fun b : Bool => (b, true)) encBool (encPair encBool encBool) :=
  (NativeCompiler.identity encBool).pair (NativeCompiler.const encBool encBool true)

/-- Exercise direct composition after the pair constructor. -/
private def pipeline :
    NativeCompiler (fun b : Bool => (b, true)) encBool (encPair encBool encBool) :=
  (NativeCompiler.identity (encPair encBool encBool)).comp tagged

/-- Decode the first frame using the total malformed-input convention, then frame that raw result.
The composition therefore exercises an input outside the image of `encFramed encBits`. -/
private def malformedReframe : NativeCompiler (fun word => frame (unframe word)) encBits encBits :=
  (NativeCompiler.encodeFrame encBits).comp NativeCompiler.unframeDecoder

-- State labels are composed constructively along with the machine terms.
example : (NativeCompiler.identity encBool).stateEncoding =
    NativeCompiler.sumStateEncoding NativeCompiler.unitStateEncoding
      NativeCompiler.rewindStateEncoding :=
  rfl

example : (NativeCompiler.const encBool encBool true).stateEncoding = Fin.valEmbedding :=
  rfl

example : (NativeCompiler.encodeFrame encBool).stateEncoding =
    NativeCompiler.sumStateEncoding
      (NativeCompiler.prodStateEncoding NativeCompiler.unitStateEncoding
        (NativeCompiler.prodStateEncoding
          (NativeCompiler.optionStateEncoding Turing.MultiTapeTM.Universal.eBit)
          Turing.MultiTapeTM.Universal.eBit))
      NativeCompiler.rewindStateEncoding :=
  rfl

example : tagged.stateEncoding =
    NativeCompiler.sumStateEncoding
      (((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).stateEncoding)
      (NativeCompiler.const encBool encBool true).stateEncoding :=
  rfl

example : pipeline.stateEncoding =
    NativeCompiler.sumStateEncoding
      (NativeCompiler.sumStateEncoding tagged.stateEncoding
        NativeCompiler.rewindWorkStateEncoding)
      (NativeCompiler.sumStateEncoding
        (NativeCompiler.sumStateEncoding NativeCompiler.markWorkStateEncoding
          (NativeCompiler.sumStateEncoding
            (NativeCompiler.identity (encPair encBool encBool)).stateEncoding
            NativeCompiler.markWorkStateEncoding))
        (NativeCompiler.sumStateEncoding NativeCompiler.unitStateEncoding
          NativeCompiler.rewindWorkStateEncoding)) :=
  rfl

-- The resource constants of the construction kernel remain visible definitionally.
example (b : Bool) :
    (NativeCompiler.identity encBool).time b = 2 * (encBool b).length + 4 ∧
    (NativeCompiler.identity encBool).workspace b = 0 ∧
    (NativeCompiler.const encBool encBool true).time b = (encBool true).length + 1 ∧
    (NativeCompiler.const encBool encBool true).workspace b = 0 ∧
    (NativeCompiler.encodeFrame encBool).time b = 4 * (encBool b).length + 8 ∧
    (NativeCompiler.encodeFrame encBool).workspace b = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example (b : Bool) : tagged.time b =
    ((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).time b +
      (NativeCompiler.const encBool encBool true).time b :=
  rfl

example (b : Bool) : tagged.workspace b =
    ((NativeCompiler.encodeFrame encBool).comp
        (NativeCompiler.identity encBool)).workspace b +
      (NativeCompiler.const encBool encBool true).workspace b +
      2 * max
        ((NativeCompiler.encodeFrame encBool).comp
          (NativeCompiler.identity encBool)).tapeCount
        (NativeCompiler.const encBool encBool true).tapeCount :=
  rfl

example (b : Bool) : pipeline.time b =
    tagged.time b +
      (NativeCompiler.identity (encPair encBool encBool)).time (b, true) +
      4 * (encPair encBool encBool (b, true)).length + 9 :=
  rfl

example (b : Bool) : pipeline.workspace b =
    tagged.workspace b +
      (NativeCompiler.identity (encPair encBool encBool)).workspace (b, true) +
      5 * (encPair encBool encBool (b, true)).length +
      (6 * max tagged.tapeCount
        (NativeCompiler.identity (encPair encBool encBool)).tapeCount + 20) :=
  rfl

/-- The constructive description records every transition of a nontrivial composed compiler. -/
example (state : pipeline.State) (input : Option Bool)
    (work : Fin pipeline.tapeCount → Option Bool) :
    pipeline.description.Holds (pipeline.table.toTM.map pipeline.stateEncoding eBit)
      (pipeline.stateEncoding state) (input.map eBit) (Option.map eBit ∘ work) :=
  pipeline.description_holds state input work

example (b : Bool) : pipeline.inputBits b = (encBool b).length :=
  rfl

example (b : Bool) :
    pipeline.outputBits b = (encPair encBool encBool (b, true)).length :=
  rfl

-- The emitted pair coordinate includes both the framing of the dynamic bit and the fixed tag.
example (b : Bool) : pipeline.outputBits b =
    2 * (encBool b).length + 1 + (encBool true).length := by
  change (encPair encBool encBool (b, true)).length = _
  exact length_encPair (b, true)

-- Both branches compute, and the checked pipeline is genuinely nonconstant.
example : pipeline.table.toTM.ComputesTidilyInTimeAndSpace
    (encBool false) (encPair encBool encBool (false, true))
    (pipeline.time false) (pipeline.workspace false) :=
  pipeline.computes false

example : pipeline.table.toTM.ComputesTidilyInTimeAndSpace
    (encBool true) (encPair encBool encBool (true, true))
    (pipeline.time true) (pipeline.workspace true) :=
  pipeline.computes true

example : frame (unframe [true]) = [false] := by
  decide

example : malformedReframe.table.toTM.ComputesTidilyInTimeAndSpace [true] [false]
    (malformedReframe.time [true]) (malformedReframe.workspace [true]) := by
  simpa [unframe, frame] using malformedReframe.computes [true]

-- The forward comparison keeps the existing plain calculus as the public consumer interface.
example : ComputableInTimeAndSpace (fun b : Bool => (b, true)) encBool
    (encPair encBool encBool) pipeline.time pipeline.workspace :=
  pipeline.computableInTimeAndSpace

example : encPair encBool encBool (false, true) ≠ encPair encBool encBool (true, true) := by
  decide

end CslibFrontierTests.Internal.NativeCompilerWitness
