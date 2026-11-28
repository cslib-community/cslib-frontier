/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BitListCodec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives

/-!
# Linear conversion between raw and framed Boolean lists

The values are unchanged: only the existing encodings differ. Framing followed by a finite-state
transducer inserts a delimiter after each bit; a second transducer removes those delimiters.
Both directions have linear time, workspace and output length, without a fold over growing words.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.bitsToList`: raw bits to framed Boolean elements.
* `Turing.MultiTapeTM.ComputableInDegree.listToBits`: framed Boolean elements to raw bits.
-/

namespace Turing.MultiTapeTM.ComputableInDegree

open Internal

/-- Convert raw bits to the existing framed Boolean-list encoding in linear time and space. -/
public theorem bitsToList : ComputableInDegree (fun word => word)
    encBits (encList encBool) 1 1 := by
  have hframe : ComputableInDegree (fun word : List Bool => word)
      encBits (encFramed encBits) 1 1 := of_frame fun _ => rfl
  have hconvert : ComputableInDegree (fun word : List Bool => word)
      (encFramed encBits) (encList encBool) 1 1 :=
    of_transducer bitsToBoolListT fun word => (bitsToBoolListT_run word).symm
  exact hconvert.comp hframe

/-- Remove Boolean-element framing in linear time and space, leaving the list unchanged. -/
public theorem listToBits : ComputableInDegree (fun word => word)
    (encList encBool) encBits 1 1 :=
  of_transducer listBitsT fun word => (listBitsT_run word).symm

end Turing.MultiTapeTM.ComputableInDegree
