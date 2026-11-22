/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Hoza
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness

/-! # Nondeterministic logarithmic space within the modular classes

Apply `NL ⊆ ModL k` through ordinary imports: directed reachability is decided by the parity of
a logspace count, and every deterministic logspace language has a witness for every modulus at
least two, in its original encoding.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.ModularNL

open Cslib.Complexity

/-- Directed reachability on adjacency matrices is decided by the parity of a logspace count. -/
example : ∃ f ∈ SharpL encSTCON, ∀ I, I ∈ STCON ↔ Odd (f I) :=
  mem_ModL_two.mp (NL_subset_ModL le_rfl STCON.mem_NL)

/-- A deterministic logspace language has a witness modulo every `k ≥ 2`, in its own encoding. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ} (hk : 2 ≤ k) (h : A ∈ L enc) :
    A ∈ ModL k enc :=
  NL_subset_ModL hk (L_subset_NL h)

end CslibFrontierTests.LogSpace.ModularNL
