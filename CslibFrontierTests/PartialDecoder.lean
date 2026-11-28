/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Partial

/-! Strict scalar and framed-stream decoding, including empty value types. -/

namespace CslibFrontierTests.PartialDecoder

open Turing.MultiTapeTM

example {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) (value : α) :
    D.decode (enc value) = some value := D.decode_enc value

example {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) (word : List Bool)
    (value : α) (h : D.decode word = some value) : enc value = word :=
  (D.decode_eq_some_iff word value).mp h

example {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) :
    ComputableInPolyTime D.decode encBits (encOption enc) := D.computable

example {α : Type} {enc : α ↪ List Bool} (D : PartialDecoder enc) :
    ComputableInPolyTime D.list.decode encBits (encOption (encList enc)) := D.list.computable

-- A total Boolean decoder accepts a default on malformed input; the strict codec rejects it.
example : (PartialDecoder.ofDecoder Decoder.bool).decode [] = none := by decide
example : (PartialDecoder.ofDecoder Decoder.bool).decode [true, false] = none := by decide
example : (PartialDecoder.ofDecoder Decoder.bool).decode [true] = some true := by decide

-- Complete list frames retain order. Empty and incomplete scalar frames are malformed.
example : (PartialDecoder.ofDecoder Decoder.bool).list.decode
      [true, true, false, true, false, false] = some [true, false] ∧
    (PartialDecoder.ofDecoder Decoder.bool).list.decode [false] = none ∧
    (PartialDecoder.ofDecoder Decoder.bool).list.decode [true] = none ∧
    (PartialDecoder.ofDecoder Decoder.bool).list.decode [true, true, false, true] = none := by
  simp [PartialDecoder.list, PartialDecoder.checked, frames_of_ne_nil, unframe, dropFrame,
    PartialDecoder.ofDecoder, Decoder.bool, frame]

example : (PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.bool)
    (PartialDecoder.ofDecoder Decoder.bool)).decode [true, true, false, false] =
      some (true, false) := by decide
example : (PartialDecoder.pair (PartialDecoder.ofDecoder Decoder.bool)
    (PartialDecoder.ofDecoder Decoder.bool)).decode [true, true, false, false, true] = none :=
  by decide

example : (PartialDecoder.sum PartialDecoder.unit (PartialDecoder.ofDecoder Decoder.bool)).decode
    [false] = some (Sum.inl ()) := by decide
example : (PartialDecoder.sum PartialDecoder.unit (PartialDecoder.ofDecoder Decoder.bool)).decode
    [false, true] = none := by decide

/-- A scalar encoding with no values, hence no valid words. -/
private def noValues : Empty ↪ List Bool := ⟨Empty.elim, fun value => Empty.elim value⟩

/-- The optional scalar type still admits a total decoder and a native constant machine. -/
private def optionalNoValues : Decoder (encOption noValues) where
  decode _ := none
  decode_enc value := by cases value with
    | none => rfl
    | some value => exact Empty.elim value
  computable := (ComputableInPolyTime.const none).exists_degree

example (word : List Bool) : (PartialDecoder.empty noValues).decode word = none :=
  (PartialDecoder.empty noValues).decode_eq_none_iff word |>.mpr (by rintro ⟨value, _⟩; cases value)

example : (PartialDecoder.ofOptionDecoder optionalNoValues).decode [] = none := by decide
example : (PartialDecoder.ofOptionDecoder optionalNoValues).list.decode [] = some [] ∧
    (PartialDecoder.ofOptionDecoder optionalNoValues).list.decode [false] = none := by
  simp [PartialDecoder.list, PartialDecoder.checked, frames_of_ne_nil, unframe, dropFrame,
    PartialDecoder.ofOptionDecoder, optionalNoValues]

end CslibFrontierTests.PartialDecoder
