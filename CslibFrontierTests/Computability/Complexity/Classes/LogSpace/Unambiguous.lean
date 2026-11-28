/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting

/-! # Unambiguous logarithmic space as a space class

Witnesses for `UL` and for `USPACE(log₂ n)` convert in both directions, and an unambiguous
witness at the bound `log₂ n` gives an `NL` witness through `NSPACE(log₂ n)`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.Unambiguous

open Cslib.Complexity

/-- An unambiguous logspace witness is an unambiguous witness at the bound `log₂ n`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ UL enc) :
    A ∈ USPACE enc Nat.log2 :=
  UL_eq_USPACE ▸ h

/-- An unambiguous witness at the bound `log₂ n` is an unambiguous logspace witness. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ USPACE enc Nat.log2) :
    A ∈ UL enc :=
  UL_eq_USPACE ▸ h

/-- An unambiguous witness at the bound `log₂ n` is an `NL` witness, through `NSPACE(log₂ n)`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ USPACE enc Nat.log2) :
    A ∈ NL enc :=
  NL_eq_NSPACE ▸ USPACE_subset_NSPACE h

end CslibFrontierTests.LogSpace.Unambiguous
