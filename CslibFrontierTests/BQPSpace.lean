/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.BQP.Classical
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Problems.Primes

set_option linter.privateModule false

/-!
# Tests: `BQP ⊆ PSPACE`

`BQP_subset_PSPACE` applied to a concrete language: the primes, in binary, are in `P` (AKS), hence
in `BQP` (`P_subset_BQP`), hence in `PSPACE`.
-/

namespace CslibFrontierTests.BQPSpace

open Cslib.Complexity Turing.MultiTapeTM

example : {n : ℕ | n.Prime} ∈ PSPACE encNat :=
  BQP_subset_PSPACE (P_subset_BQP primes_mem_P)

end CslibFrontierTests.BQPSpace
