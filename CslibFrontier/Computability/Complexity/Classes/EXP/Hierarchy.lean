/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH

/-!
# The linear-exponent exponential hierarchy

`EH` is the bounded-alternation presentation of the weak exponential hierarchy
[Hemaspaandra1989]. The verifier runs in polynomial time in the complete instance and
certificate length. On the quantified domain the certificate has length `2 ^ O(n)`, so this
gives linear-exponent time overall. An unused existential block permits deterministic
exponential-time checking even when no actual guesses are needed.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The weak linear-exponent exponential hierarchy has a fixed number of alternating
quantifiers over exponentially long words, starting existentially, and a uniform verifier. -/
@[expose] def EH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k c : ℕ) (V : Set (α × List Bool)), V ∈ P (encPair enc encBits) ∧ ∀ a,
    a ∈ A ↔ Alternation true (List.replicate (k + 1) (2 ^ (c * (enc a).length)))
      (fun w => (a, w) ∈ V)}

end Cslib.Complexity
