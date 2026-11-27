/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Countable

/-! Checked clients of Goldreich, Theorem 1.4 (draft `r1.pdf` of 30 December 2006): the
computable functions on bit strings are countable while all functions form a continuum, so some
function on bit strings is not computable, and countability holds for every encoding. -/

set_option linter.privateModule false

namespace CslibFrontierTests.GoldreichCountable

open Turing.MultiTapeTM

/-- Some function from bit strings to bit strings is not computable by a native machine. -/
example : ∃ f : List Bool → List Bool, ¬IsComputable f encBits encBits := by
  by_contra! h
  obtain ⟨hc, hmk⟩ := countable_setOf_isComputable_and_mk_eq_continuum
  have : Countable (List Bool → List Bool) := by
    rw [show {f : List Bool → List Bool | IsComputable f encBits encBits} = Set.univ from
      Set.eq_univ_of_forall h] at hc
    exact Set.countable_univ_iff.mp hc
  have := Cardinal.mk_le_aleph0_iff.mpr this
  rw [hmk] at this
  exact absurd this (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- Countability holds for arbitrary encodings, here functions from bit strings to Booleans. -/
example : {f : List Bool → Bool | IsComputable f encBits encBool}.Countable :=
  countable_setOf_isComputable encBits encBool

end CslibFrontierTests.GoldreichCountable
