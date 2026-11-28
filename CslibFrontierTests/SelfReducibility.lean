/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.TFNP.SelfReducibility

/-! Checked clients of Goldreich's Exercises 2.14(1), 2.16 and 2.17. Exercise 2.14(1) for
instances that are words uses `Decoder.bits`. The divisor relation has solutions on a concrete
composite number and none on a prime. A satisfiable instance of `SearchSelfReducible` exists, so
the non-self-reducibility conclusions are not vacuous. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SelfReducibility

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- Exercise 2.14(1) for instances that are words. -/
example (hne : P encBits ≠ NP encBits ∩ coNP encBits) :
    ∃ R ∈ FNP encBits, IsTotalSearch R ∧ R ∉ FPSearch encBits ∧
      ¬SearchSelfReducible encBits R :=
  exists_mem_FNP_not_selfReducible Decoder.bits hne

/-- `3` is a non-trivial divisor of `6`. -/
example : divisorSearch 6 (encNat 3) := ⟨3, rfl, by decide, by decide, by decide⟩

/-- A prime has no non-trivial divisor. -/
example (w : List Bool) : ¬divisorSearch 7 w := fun h =>
  (Set.ext_iff.mp searchDomain_divisorSearch 7).mp ⟨w, h⟩ |>.2 (by decide)

/-- `SearchSelfReducible` holds for some relation with the composite numbers as domain. -/
example : SearchSelfReducible encNat compositeSearch :=
  .of_mem_FPSearch compositeSearch_mem_FPSearch

end CslibFrontierTests.SelfReducibility
