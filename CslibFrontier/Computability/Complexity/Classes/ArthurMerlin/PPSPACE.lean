/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games.PolyRounds

/-!
# Public-coin interactive proofs with polynomially many moves

`PPSPACE` uses public randomness during a polynomial number of interactions. It shares the
unbounded-error threshold of `IPP`, with public-coin game values used for acceptance.

## References

* [Complexity Zoo, PPSPACE](https://complexityzoo.net/Complexity_Zoo:P#ppspace)
* [C. Papadimitriou, *Computational Complexity*, §19.2][Papadimitriou94]
-/

namespace Cslib.Complexity

open Turing.MultiTapeTM AMGame

/-- The public-coin interactive proof class with a polynomial-time schedule and verifier.
Membership is equivalent to the optimal acceptance probability being strictly above one half. -/
@[expose] public def PPSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (shape : ℕ → List (AMMove × ℕ)) (V : α × List Bool → Bool),
    ComputableInPolyTime shape encUnary encAMShape ∧
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, a ∈ A ↔ 1 / 2 < value true (shape (enc a).length) (fun t => (V (a, t)).toNat)}

end Cslib.Complexity
