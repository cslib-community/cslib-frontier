/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Strict partial decoders

`PartialDecoder enc` decodes precisely the image of the explicitly chosen embedding `enc`.
It returns `none` on every other word and supplies a native polynomial-time machine certificate.
The value type may be empty. The certificate is an additional resource assumption on a scalar
codec; an arbitrary embedding alone supplies no decoder or resource bound.

The constructors `unit`, `empty`, `pair`, `sum`, and `list` follow the existing encoding layouts.
Pairs frame their first field; sums add one Boolean tag; lists frame every element in order.
The existing `frames` parser supplies list splitting. Reencoding checks reject incomplete frames,
noncanonical scalar words, and unconsumed bits. Syntax-level rejection of extra complete tokens
belongs to the prefix parser using the resulting token-list codec.

`checked` upgrades a certified candidate decoder with a round-trip law to a strict decoder.
`ofDecoder` and `ofOptionDecoder` reuse existing total decoders; the latter supports an empty
value type because only its option type must have a total decoder. Every composition carries a
native polynomial time and space certificate; no claim about arbitrary recursive functions is
made.
-/

public section

namespace Turing.MultiTapeTM

/-- A strict decoder with a native polynomial-time certificate on every input word. -/
structure PartialDecoder {α : Type} (enc : α ↪ List Bool) where
  /-- The decoded value, or `none` on a word outside the encoding's image. -/
  decode : List Bool → Option α
  /-- Successful decoding characterizes exactly the chosen word layout. -/
  decode_eq_some_iff (word : List Bool) (value : α) : decode word = some value ↔ enc value = word
  /-- Native polynomial time and space, with the decoded output charged in `encOption enc`. -/
  computable : ComputableInPolyTime decode encBits (encOption enc)

namespace PartialDecoder

variable {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool}

/-- Every encoded value is accepted and recovered. -/
@[simp] theorem decode_enc (D : PartialDecoder enc) (value : α) :
    D.decode (enc value) = some value :=
  (D.decode_eq_some_iff _ _).mpr rfl

/-- A word is rejected exactly when it is outside the image of the chosen embedding. -/
theorem decode_eq_none_iff (D : PartialDecoder enc) (word : List Bool) :
    D.decode word = none ↔ ¬ ∃ value, enc value = word := by
  simp only [Option.eq_none_iff_forall_not_mem, Option.mem_def, D.decode_eq_some_iff,
    not_exists]

/-- Add a canonical-word check to a certified candidate decoder. The supplied law is only a
round trip; arbitrary malformed candidate outputs are checked before acceptance. -/
@[expose] def checked (candidate : List Bool → Option α)
    (roundtrip : ∀ value, candidate (enc value) = some value)
    (computable : ComputableInPolyTime candidate encBits (encOption enc)) : PartialDecoder enc where
  decode word :=
    (candidate word).elim none fun value => if enc value = word then some value else none
  decode_eq_some_iff word value := by
    constructor
    · intro h
      cases hc : candidate word with
      | none => simp [hc] at h
      | some found =>
        simp only [hc, Option.elim_some] at h
        split_ifs at h with hw
        · cases Option.some.inj h
          exact hw
    · intro h
      subst word
      simp [roundtrip]
  computable := by
    have hword := ComputableInPolyTime.fst encBits enc
    have hvalue := ComputableInPolyTime.snd encBits enc
    have hbits : ComputableInPolyTime (fun p : List Bool × α => enc p.2)
        (encPair encBits enc) encBits := hvalue.of_enc_eq fun _ => rfl
    have htest := hbits.decide_eq' hword
    have hbody := ComputableInPolyTime.ite_decide htest
      ((ComputableInPolyTime.optionSome enc).comp hvalue) (ComputableInPolyTime.const none)
    exact computable.optionElimWithInput (ComputableInPolyTime.const none) hbody

/-- Make an existing total decoder strict by checking the complete encoded word. -/
@[expose] def ofDecoder (D : Decoder enc) : PartialDecoder enc :=
  checked (fun word => some (D.decode word))
    (fun value => by rw [D.decode_enc])
    ((ComputableInPolyTime.optionSome enc).comp D.computableInPolyTime)

/-- Use a total decoder of optional values without requiring an inhabitant of the value type.
The added `true` bit is the existing `encOption` tag and is not part of the scalar layout. -/
@[expose] def ofOptionDecoder (D : Decoder (encOption enc)) : PartialDecoder enc :=
  checked (fun word => D.decode (true :: word))
    (fun value => by simpa only [encOption_some] using D.decode_enc (some value))
    (D.computableInPolyTime.comp
      (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) ComputableInPolyTime.id'))

/-- The unit word is the empty word; every nonempty word is rejected. -/
@[expose] def unit : PartialDecoder encUnit :=
  checked (fun _ => some ()) (fun _ => rfl) (ComputableInPolyTime.const (some ()))

/-- An empty scalar type rejects every word, without choosing a fallback value. -/
@[expose] def empty (encoding : α ↪ List Bool) [IsEmpty α] : PartialDecoder encoding where
  decode _ := none
  decode_eq_some_iff _ value := isEmptyElim value
  computable := ComputableInPolyTime.const none

/-- Decode a framed first field followed by the second field, retaining scalar order. -/
@[expose] def pair (left : PartialDecoder enc) (right : PartialDecoder enc') :
    PartialDecoder (encPair enc enc') :=
  checked
    (fun word => (left.decode (unframe word)).elim none fun a =>
      (right.decode (dropFrame word)).map fun b => (a, b))
    (fun value => by
      simp [unframe_frame_append, dropFrame_frame_append])
    (by
      have hleft := left.computable.comp
        Internal.DecoderWords.unframe_degree.computableInPolyTime
      have hright := right.computable.comp
        Internal.DecoderWords.dropFrame_degree.computableInPolyTime
      exact hleft.optionPair hright)

/-- Decode the existing one-bit sum tag and the selected scalar payload. -/
@[expose] def sum (left : PartialDecoder enc) (right : PartialDecoder enc') :
    PartialDecoder (encSum enc enc') :=
  checked
    (fun word => if word.headD false then (right.decode word.tail).map Sum.inr
      else (left.decode word.tail).map Sum.inl)
    (fun value => by cases value <;> simp)
    (by
      have hleft := left.computable.comp Internal.DecoderWords.tail_degree.computableInPolyTime
      have hright := right.computable.comp Internal.DecoderWords.tail_degree.computableInPolyTime
      have hl := hleft.optionMapWithInput (f := fun (_ : List Bool) (a : α) => Sum.inl (β := β) a)
        ((ComputableInPolyTime.sumInl enc enc').comp (ComputableInPolyTime.snd encBits enc))
      have hr := hright.optionMapWithInput (f := fun (_ : List Bool) (b : β) => Sum.inr (α := α) b)
        ((ComputableInPolyTime.sumInr enc enc').comp (ComputableInPolyTime.snd encBits enc'))
      exact Internal.DecoderWords.bool_degree.computableInPolyTime.ite hr hl)

private theorem optionToList_computable (encoding : α ↪ List Bool) :
    ComputableInPolyTime (fun value : Option α => value.toList) (encOption encoding)
      (encList encoding) := by
  have h := (ComputableInPolyTime.id' (encIn := encOption encoding)).optionElimWithInput
    (body := fun (_ : Option α) (value : α) => [value])
    (ComputableInPolyTime.const ([] : List α))
    (ComputableInPolyTime.cons' (ComputableInPolyTime.snd (encOption encoding) encoding)
      (ComputableInPolyTime.const []))
  convert h using 1
  funext value
  cases value <;> rfl

/-- Decode every framed element with the supplied scalar codec and check the complete list
word. Empty element types are supported, and malformed final frames are rejected. -/
@[expose] def list (D : PartialDecoder enc) : PartialDecoder (encList enc) :=
  checked
    (fun word => some ((frames word).flatMap fun bits => (D.decode bits).toList))
    (fun values => by
      rw [frames_encList, List.flatMap_map]
      simp)
    (by
      have hflat : ComputableInPolyTime
          (fun word => (frames word).flatMap fun bits => (D.decode bits).toList)
          encBits (encList enc) :=
        ComputableInPolyTime.flatMapWithInput computableInDegree_frames.computableInPolyTime
          ((optionToList_computable enc).comp
            (D.computable.comp (ComputableInPolyTime.snd encBits encBits)))
      exact (ComputableInPolyTime.optionSome (encList enc)).comp hflat)

end PartialDecoder
end Turing.MultiTapeTM
