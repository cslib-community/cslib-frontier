/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Modular
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness

/-! # Modular counting in logarithmic space

Apply `NL ⊆ ModL k` through ordinary imports: directed reachability and every deterministic
logspace language get a parity witness in their original encoding, and a witness for every
modulus at least two. Modulus one accepts no instance.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.Modular

open Cslib.Complexity

/-- Directed reachability on adjacency matrices is decided by the parity of a logspace count. -/
example : ∃ f ∈ SharpL encSTCON, ∀ I, I ∈ STCON ↔ Odd (f I) :=
  mem_ModL_two.mp (NL_subset_ModL le_rfl STCON.mem_NL)

/-- A deterministic logspace language has a witness modulo every `k ≥ 2`, in its own encoding. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ} (hk : 2 ≤ k) (h : A ∈ L enc) :
    A ∈ ModL k enc :=
  NL_subset_ModL hk (L_subset_NL h)

/-- An unambiguous witness is a modular witness without passing through `NL = UL`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ UL enc) : A ∈ ModL 3 enc :=
  UL_subset_ModL (by decide) h

/-- Every residue modulo one is zero, so modulus one accepts no instance. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ ModL 1 enc) : A = ∅ := by
  obtain ⟨f, -, hA⟩ := h
  ext a
  simpa [Nat.mod_one] using hA a

end CslibFrontierTests.LogSpace.Modular
