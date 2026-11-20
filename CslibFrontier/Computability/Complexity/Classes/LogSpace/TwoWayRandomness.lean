/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Operators
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Logarithmic space with rereadable random bits

`BPDotL` and `ZPDotL` give a deterministic logspace machine the instance and a uniformly
sampled polynomial-length random string as one read-only input. The random bits can be
reread. `ZPDotL` allows abstention and guarantees that every definitive answer is correct.

## References

* [Complexity Zoo, BP·L](https://complexityzoo.net/Complexity_Zoo:B#bpdotl)
* [Complexity Zoo, ZP·L](https://complexityzoo.net/Complexity_Zoo:Z)
* [S. Arora and B. Barak, *Computational Complexity*, Section 7.7][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- Bounded-error logarithmic space with a polynomial-length rereadable random input. -/
def BPDotL (enc : α ↪ List Bool) : Set (Set α) :=
  BPOp enc (L (encPair enc encBits))

/-- Zero-error logarithmic space with a polynomial-length rereadable random input.
On every supported random string the machine gives a correct answer or abstains.
At least two thirds of the random strings give a definitive answer. -/
def ZPDotL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Option Bool),
    ComputableInLogSpace V (encPair enc encBits) (encOption encBool) ∧
      (∀ a r, r.length = p.eval (enc a).length → ∀ b, V (a, r) = some b → (a ∈ A ↔ b = true)) ∧
      ∀ a, 2 * 2 ^ p.eval (enc a).length ≤
        3 * acceptCount (fun x => (V x).isSome) a (p.eval (enc a).length)}

end Cslib.Complexity
