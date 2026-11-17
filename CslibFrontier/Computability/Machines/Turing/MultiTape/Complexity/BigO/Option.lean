/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OOptionPrimitives

/-!
# Parameterized option elimination with retained input

The arbitrary-resource rule `Turing.MultiTapeTM.ComputableInO.optionElimWithInput` is provided
by the native option primitives, also used by polynomial-time option elimination. This entry
point retains the quantitative `fun_prop` calculus for existing clients. The selected handler
receives the original input and its payload; time and charged space remain independent.
-/

public section

attribute [fun_prop] Turing.MultiTapeTM.ComputableInO.optionElimWithInput

namespace Turing.MultiTapeTM.ComputableInO

/-- Tagged-option search rule fixing the intermediate format before checking the handler.
Resource accounting is exactly the generic capability theorem's accounting. -/
@[fun_prop]
theorem optionElimWithInputTagged {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    {Tv Sv Tnone Snone : α → ℕ} {Tbody Sbody : α × β → ℕ}
    (hv : ComputableInO value encA (encOption encB) Tv Sv)
    (hn : ComputableInO fallback encA encC Tnone Snone)
    (hb : ComputableInO (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC Tbody Sbody) :
    ComputableInO (fun a => (value a).elim (fallback a) (body a)) encA encC
      (fun a => 2 * Tv a + (encA a).length +
        (value a).elim (Tnone a) (fun b => Tbody (a, b)))
      (fun a => 2 * Sv a + (encA a).length +
        (value a).elim (Snone a) (fun b => Sbody (a, b))) :=
  optionElimWithInput (encB := encB) (encO := encOption encB) hv hn hb

end Turing.MultiTapeTM.ComputableInO
