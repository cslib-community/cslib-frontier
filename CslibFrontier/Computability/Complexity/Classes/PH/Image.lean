/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.Classes.PH.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Encoded languages at each existential level

A polynomial-time decoder transfers membership and Karp completeness to raw words. Malformed
words are rejected by checking that decoding and re-encoding returns the original word.
## Main results

* `mem_SigmaP_image`: membership of an encoded image with a decoder.
* `SigmaPComplete.image`: completeness of that raw-word image.

-/

public section
namespace Cslib.Complexity
open Turing.MultiTapeTM
variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {A : Set α}

/-- Encoding a `Σₖ` problem with a polynomial-time decoder gives a raw-word `Σₖ` language. -/
theorem mem_SigmaP_image (D : Decoder enc) (hA : A ∈ SigmaP k enc) :
    enc '' A ∈ SigmaP k encBits := by
  have henc : ComputableInPolyTime enc enc encBits := .id'
  have hvalid : {w | enc (D.decode w) = w} ∈ P encBits :=
    ⟨fun w => decide (enc (D.decode w) = w), by fun_prop, by simp⟩
  have hpre := (show PolyTimeReducible encBits enc {w | D.decode w ∈ A} A from
    ⟨D.decode, D.computableInPolyTime, fun _ => Iff.rfl⟩).mem_SigmaP hA
  convert inter_mem_SigmaP (SigmaP_mono (Nat.zero_le k) (SigmaP_zero ▸ hvalid)) hpre using 1
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [D.decode_enc, ha]
  · rintro ⟨hw, ha⟩
    exact ⟨D.decode w, ha, hw⟩

/-- A complete encoded `Σₖ` problem yields a complete raw-word oracle, rejecting malformed words. -/
theorem SigmaPComplete.image (hA : SigmaPComplete k enc A) (D : Decoder enc) :
    SigmaPComplete k encBits (enc '' A) := by
  refine ⟨mem_SigmaP_image D hA.1, fun {β} encB B hB => (hA.2 encB B hB).trans ?_⟩
  exact ⟨enc, .id', fun a => by simp only [Set.mem_image, enc.injective.eq_iff, exists_eq_right]⟩

end Cslib.Complexity
