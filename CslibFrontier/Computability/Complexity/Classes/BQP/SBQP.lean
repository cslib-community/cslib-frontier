/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BQP

/-!
# Small bounded-error quantum polynomial time

In the uniform circuit model of `BQP`, `SBQP` allows an exponentially small acceptance
threshold, with a factor of two separating the two cases [Kuperberg][Kuperberg2015].
Kuperberg's circuit characterization uses Hadamard and Toffoli gates.

## Main definitions

* `SBQP`: small bounded-error quantum polynomial time.
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum

/-- Yes-instances are accepted with probability at least `2⁻ᵖ⁽ⁿ⁾`, and no-instances with
probability at most half that threshold, for one polynomial `p` in the encoded length `n`. -/
def SBQP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformCircuitFamily, ∃ p : Polynomial ℕ, ∀ a,
    (a ∈ A → 1 / (2 : ℝ) ^ p.eval (enc a).length ≤ F.acceptProb (enc a)) ∧
    (a ∉ A → F.acceptProb (enc a) ≤ 1 / (2 : ℝ) ^ (p.eval (enc a).length + 1))}


end Cslib.Complexity
