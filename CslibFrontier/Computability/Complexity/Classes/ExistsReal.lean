/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Real complexity classes defined by polynomial-time reductions

`ExistsReal enc` and `ExistsForallReal enc` are the polynomial-time many-one downward
closures of ETR and existential–universal real truth. Reductions are total on source
instances. Specializing to raw bitstrings recovers the classes in `edemaine/lean-canny`'s
formal abstract at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Hardness and completeness use `PolyTimeHard` and `PolyTimeComplete` directly.
This module provides the class definitions; their counting-hierarchy bounds are separate.

## Main definitions

* `Cslib.Complexity.ExistsReal`: problems reducible to existential real truth.
* `Cslib.Complexity.ExistsForallReal`: problems reducible to two-block real truth.
-/

public section
namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Problems polynomial-time many-one reducible to the encoded ETR language. -/
@[expose] def ExistsReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | PolyTimeReducible enc encBits L ETR}

/-- Problems polynomial-time many-one reducible to encoded existential–universal real truth. -/
@[expose] def ExistsForallReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | PolyTimeReducible enc encBits L ExistsForallTheory}

end Cslib.Complexity
