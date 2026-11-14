/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Total decoding of tagged sums

The first bit chooses the summand and the remainder is decoded by its supplied decoder. This topic
module keeps tagged-sum construction out of the lower-fan-out basic decoder module.

## Main definitions

* `Turing.MultiTapeTM.Decoder.sum`: total decoding of `encSum`.

## Main results

The decoder's `Decoder.decode_enc` field proves that it retracts `encSum`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Decoder

/-- Tagged sums are decoded according to their first bit. Empty and malformed words select the
left summand, consistently with `Decoder.bool`. -/
def sum {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} (D₁ : Decoder enc₁)
    (D₂ : Decoder enc₂) : Decoder (encSum enc₁ enc₂) where
  decode w := if w.headD false then .inr (D₂.decode w.tail) else .inl (D₁.decode w.tail)
  decode_enc s := by cases s <;> simp [D₁.decode_enc, D₂.decode_enc]
  computable := by
    have htail := Internal.DecoderWords.tail_degree.computableInPolyTime
    have hleft := (ComputableInPolyTime.sumInl enc₁ enc₂).comp
      (D₁.computableInPolyTime.comp htail)
    have hright := (ComputableInPolyTime.sumInr enc₁ enc₂).comp
      (D₂.computableInPolyTime.comp htail)
    exact (ComputableInPolyTime.ite Internal.DecoderWords.bool_degree.computableInPolyTime
      hright hleft).exists_degree

end Turing.MultiTapeTM.Decoder
