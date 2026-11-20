/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Algebraic

/-!
# Zero-error quantum polynomial time

`ZQP` uses the algebraic-amplitude convention of
[Buhrman, de Wolf][BuhrmanDeWolf2003ZeroError], §2. One fixed finite gate set is chosen
for the entire family. Approximate simulation by the gate set of `BQP` need not preserve
a zero probability, so the circuit generator describes gates by their labels in that set.

## Main definitions

* `Cslib.Complexity.ZQP`: zero-error decision with probability at most one half of abstaining.
-/

@[expose] public section

namespace Cslib.Complexity

open Quantum

/-- The languages with a polynomial-time uniform algebraic circuit family that returns the correct
answer with probability at least one half and returns the wrong answer with probability zero. -/
def ZQP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ F : UniformAlgebraicCircuitFamily, ∀ a,
    (a ∈ A → 1 / 2 ≤ F.answerProb (enc a) true ∧ F.answerProb (enc a) false = 0) ∧
    (a ∉ A → 1 / 2 ≤ F.answerProb (enc a) false ∧ F.answerProb (enc a) true = 0)}

end Cslib.Complexity
