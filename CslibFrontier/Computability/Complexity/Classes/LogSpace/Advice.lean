/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting

/-!
# Polynomial advice for logspace counting

`SharpLPoly` supplies arbitrary length-dependent polynomial advice as part of the read-only
input. The underlying machine counts accepting branches with workspace logarithmic in the
combined encoded length.

## References

* [Complexity Zoo, nonuniform #L](https://complexityzoo.net/Complexity_Zoo:Symbols)
* [O. Goldreich, *Computational Complexity*, exact-length advice][Goldreich2007DraftR2]
-/

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Nonuniform `SharpL`: exactly `p(n)` arbitrary bits of advice are used at input length `n`. -/
@[expose] public def SharpLPoly : Set (List Bool → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (advice : ℕ → List Bool),
    (∀ n, (advice n).length = p.eval n) ∧
    ∃ F ∈ SharpL (encPair encBits encBits), ∀ x, f x = F (advice x.length, x)}

end Cslib.Complexity
