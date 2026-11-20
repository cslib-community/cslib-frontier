/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.GraphIsomorphism
public import CslibFrontier.Computability.Complexity.Reduction.Turing

/-!
# Graph isomorphism under polynomial-time Turing reductions

`Cslib.Complexity.GI` is the class of languages decidable in polynomial time with an oracle for
simple graph isomorphism.
-/

public section

namespace Cslib.Complexity

/-- The languages polynomial-time Turing reducible to simple graph isomorphism. -/
def GI {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PolyTimeTuringReducible enc encGraphIsomorphism A GraphIsomorphism}

end Cslib.Complexity
