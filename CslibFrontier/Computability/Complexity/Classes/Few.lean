/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-!
# Polynomially bounded accepting counts with a decision predicate

`Cslib.Complexity.Few` is the class of languages whose membership can be decided in polynomial time
given the polynomially bounded accepting count of a nondeterministic polynomial-time computation
[Cai and Hemachandra][CaiHemachandra1990].
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Languages decided by a polynomial-time predicate of the input and a polynomially bounded
`#P` count for that input. -/
def Few {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → ℕ) (p : Polynomial ℕ) (V : α × ℕ → Bool),
    f ∈ SharpP enc ∧ (∀ a, f a ≤ p.eval (enc a).length) ∧
      ComputableInPolyTime V (encPair enc encNat) encBool ∧
      ∀ a, a ∈ A ↔ V (a, f a) = true}

end Cslib.Complexity
