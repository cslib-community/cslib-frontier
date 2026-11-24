/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Space

/-!
# Unambiguous space classes

`Cslib.Complexity.USPACE enc s` consists of the problems decided unambiguously within space
`O(s n)`: one finite-state binary counting machine has exactly one accepting branch on members
and none on nonmembers, on instances whose encoding under `enc` has length `n`. As for
`Cslib.Complexity.NSPACE`, the bound `c₁ * s n + c₂` holds along every computation prefix,
including rejecting branches, every branch halts, the input tape is read-only and the output tape
write-only. Branches are transition-occurrence traces of the counting machine, so two equal
transitions at one configuration count twice.

Forgetting transition multiplicity gives `USPACE(s) ⊆ NSPACE(s)` for every bound `s`. The
logarithmic case is `Cslib.Complexity.UL`, by `Cslib.Complexity.UL_eq_USPACE`.

## Main definitions

* `Cslib.Complexity.USPACE`: unambiguous space classes.

## Main results

* `Cslib.Complexity.USPACE_subset_NSPACE`: an unambiguous decider is a nondeterministic one.
-/

public section

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool} {s : ℕ → ℕ}

/-- The problems decided unambiguously within space `O(s n)`, that is `c₁ * s n + c₂`: one
finite-state binary counting machine, along every computation prefix and with every branch
halting, has one accepting branch on members and none on nonmembers, on instances whose encoding
under `enc` has length `n`. -/
@[expose] def USPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeCTM k Bool State) (c₁ c₂ : ℕ)
    (f : α → ℕ), (M.CountsInSpace enc f fun a => c₁ * s (enc a).length + c₂) ∧
      (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- **Unambiguous space is within nondeterministic space**, for every space bound: forgetting
transition multiplicity turns the counting machine into a nondeterministic decider within the
same space. -/
theorem USPACE_subset_NSPACE : USPACE enc s ⊆ NSPACE enc s := by
  rintro A ⟨k, State, hfinite, M, c₁, c₂, f, hM, -, hA⟩
  exact ⟨k, State, hfinite, M.toNTM, c₁, c₂, hM.decidesInSpace hA⟩

end Cslib.Complexity
