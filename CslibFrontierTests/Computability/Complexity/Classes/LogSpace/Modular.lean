/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Modular

/-! # Modular counting in logarithmic space

The modular classes are used here through `Classes.LogSpace.Modular` alone, without the
`NL = UL` development: an unambiguous witness is a witness for every modulus at least two, and
gives an odd-count witness at modulus two. Modulus one accepts no instance.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.Modular

open Cslib.Complexity

/-- An unambiguous witness is a modular witness for every `k ≥ 2`, in its own encoding. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ} (hk : 2 ≤ k) (h : A ∈ UL enc) :
    A ∈ ModL k enc :=
  UL_subset_ModL hk h

/-- At modulus two the witness is a logspace count that is odd exactly on members. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ UL enc) :
    ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ Odd (f a) :=
  mem_ModL_two.mp (UL_subset_ModL le_rfl h)

/-- Every residue modulo one is zero, so modulus one accepts no instance. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ ModL 1 enc) : A = ∅ := by
  obtain ⟨f, -, hA⟩ := h
  ext a
  simpa [Nat.mod_one] using hA a

end CslibFrontierTests.LogSpace.Modular
