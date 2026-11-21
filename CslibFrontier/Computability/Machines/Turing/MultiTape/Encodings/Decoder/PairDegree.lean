/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic

/-! # Resource degrees of framed pair decoding -/

public section

namespace Turing.MultiTapeTM.Decoder

/-- Reading both frames adds a linear scan. The larger component degree controls the output. -/
theorem pair_computableInDegree {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    (A : Decoder encA) (B : Decoder encB) {d₁ e₁ d₂ e₂ : ℕ}
    (hA : ComputableInDegree A.decode encBits encA d₁ e₁)
    (hB : ComputableInDegree B.decode encBits encB d₂ e₂) :
    ComputableInDegree (A.pair B).decode encBits (encPair encA encB)
      (max 1 (max d₁ d₂)) (max e₁ e₂) := by
  exact ((hA.comp Internal.DecoderWords.unframe_degree).prod
    (hB.comp Internal.DecoderWords.dropFrame_degree)).mono (by omega) (by omega)

end Turing.MultiTapeTM.Decoder
