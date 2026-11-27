/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Time.LasVegas

/-! Clients of the Las Vegas characterisation of `ZPP`: problems in `RP ∩ coRP` are decided with
zero error in expected polynomial time, and the draft's `ZPP` is closed under complement. -/

set_option linter.privateModule false

namespace CslibFrontierTests.LasVegasZPP

open Cslib Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- A problem in `RP ∩ coRP` has a zero-error machine in expected polynomial time. -/
example {A : Set α} (hA : A ∈ RP enc) (hAc : A ∈ coRP enc) : ∃ d, A ∈ ZTIME enc (· ^ d) := by
  have hmem : A ∈ ⋃ d, ZTIME enc (· ^ d) := by
    rw [iUnion_ZTIME_pow_eq_RP_inter_coRP]
    exact ⟨hA, hAc⟩
  simpa only [Set.mem_iUnion] using hmem

/-- The draft's `ZPP` is closed under complement, through the library's `ZPP`. -/
example {A : Set α} {d : ℕ} (hA : A ∈ ZTIME enc (· ^ d)) : ∃ d', Aᶜ ∈ ZTIME enc (· ^ d') :=
  mem_ZPP_iff_exists_mem_ZTIME_pow.mp (compl_mem_ZPP (ZTIME_pow_subset_ZPP d hA))

end CslibFrontierTests.LasVegasZPP
