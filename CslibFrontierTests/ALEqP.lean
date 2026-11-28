/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.Alternation.LogSpaceGame
import CslibFrontier.Computability.Complexity.Classes.Alternation.TimeInSpace
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests: `AL = P`

`AL = P` (`Cslib.Complexity.AL_eq_P`) at the identity encoding of words, its form with the
parametric class `ASPACE (log₂ n)`, and a nonvacuity witness: the words starting with `true`,
neither empty nor everything, are in `P` and hence decided by an alternating machine within
logarithmic space (`Cslib.Complexity.P_subset_AL`). The hypotheses of
`Cslib.Complexity.DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible` hold for `s n = n` and
at the sharp edge `s n = ⌊log₂ n⌋` of its hypothesis `⌊log₂ n⌋ ≤ s n`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ALEqP

open Cslib.Complexity Turing.MultiTapeTM

example : AL encBits = P encBits := AL_eq_P

/-- `ASPACE (log₂ n)` is `P`. -/
example {α : Type} {enc : α ↪ List Bool} : ASPACE enc Nat.log2 = P enc :=
  AL_eq_ASPACE.symm.trans AL_eq_P

/-- The words starting with `true`. -/
private def StartsTrue : Set (List Bool) := {w | w.headD false = true}

/-- `StartsTrue` is neither empty nor everything. -/
example : [true] ∈ StartsTrue ∧ [] ∉ StartsTrue := by
  simp [StartsTrue]

/-- **Nonvacuity**: `StartsTrue` is in `P`, so an alternating machine decides it within space
`c * (log₂ n + 1)`, every branch halting. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : Turing.MultiTapeATM k Bool State)
    (c : ℕ), atm.DecidesInSpace encBits StartsTrue fun w => c * (Nat.log2 w.length + 1) :=
  P_subset_AL (show StartsTrue ∈ P encBits from
    ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- The hypotheses of the space-constructible form of `DTIME(2 ^ O(s)) ⊆ ASPACE(s)` are satisfiable:
at `s n = n` it gives `DTIME(2 ^ (c * n)) ⊆ ASPACE(n)`. -/
example (c : ℕ) : DTIME encBits (fun n => 2 ^ (c * n)) ⊆ ASPACE encBits fun n => n :=
  DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible spaceConstructible_id Nat.log2_le_self c

/-- At the sharp edge `s n = ⌊log₂ n⌋` of the hypothesis `⌊log₂ n⌋ ≤ s n`, the space-constructible
form gives `DTIME(2 ^ (c * ⌊log₂ n⌋)) ⊆ ASPACE(⌊log₂ n⌋)`. -/
example (c : ℕ) : DTIME encBits (fun n => 2 ^ (c * Nat.log2 n)) ⊆ ASPACE encBits Nat.log2 :=
  DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible spaceConstructible_log2 (fun _ => le_rfl) c

end CslibFrontierTests.ALEqP
