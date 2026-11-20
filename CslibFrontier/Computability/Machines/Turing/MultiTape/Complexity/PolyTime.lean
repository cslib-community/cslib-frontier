/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-!
# Polynomial-time encoding conversions

The closure rules come from the direct plain machine providers. `EncodingEquiv` expresses
conversion in both directions using independent polynomial time and space certificates.
-/

namespace Turing.MultiTapeTM

/-! ### Equivalent encodings -/

/-- Encodings that convert into each other in polynomial time. -/
public def EncodingEquiv {α : Type*} (enc₁ enc₂ : α ↪ List Bool) : Prop :=
  ComputableInPolyTime id enc₁ enc₂ ∧ ComputableInPolyTime id enc₂ enc₁

namespace EncodingEquiv

variable {α β : Type*} {enc₁ enc₂ enc₃ : α ↪ List Bool}

@[refl]
public theorem refl (enc : α ↪ List Bool) : EncodingEquiv enc enc :=
  ⟨.of_eq fun _ => rfl, .of_eq fun _ => rfl⟩

@[symm]
public theorem symm (h : EncodingEquiv enc₁ enc₂) : EncodingEquiv enc₂ enc₁ := ⟨h.2, h.1⟩

@[trans]
public theorem trans (h₁₂ : EncodingEquiv enc₁ enc₂) (h₂₃ : EncodingEquiv enc₂ enc₃) :
    EncodingEquiv enc₁ enc₃ :=
  ⟨h₂₃.1.comp h₁₂.1, h₁₂.2.comp h₂₃.2⟩

end EncodingEquiv

end Turing.MultiTapeTM
