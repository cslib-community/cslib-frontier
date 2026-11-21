/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting

/-!
# Counting and unambiguous logarithmic space

`SharpL` counts first-halting accepting occurrence traces of one finite native counting
machine. The work-tape space bound applies to every computation prefix. On each encoded
input an all-branches clock guarantees that the count includes every accepting occurrence.
Identical transitions at one configuration can still contribute distinct occurrences.

`UL` consists of the languages whose membership bit is represented by such an accepting
count. Forgetting transition multiplicities retains acceptance and the same space bound,
giving the inclusion in `NL`.

## Main definitions

* `Turing.MultiTapeCTM.CountsInLogSpace`: a logspace accepting-count witness for a fixed machine.
* `Cslib.Complexity.SharpL`: accepting occurrence counts of native logspace machines.
* `Cslib.Complexity.UL`: languages decided by such counts bounded by one.

## Main results

* `Cslib.Complexity.UL_subset_NL`: forgetting accepting branch multiplicity gives an NL decider.
-/

public section

namespace Cslib.Complexity

open Turing

variable {α : Type}

/-- A given counting machine realizes the accepting count in logarithmic workspace.
The finite clock is chosen for each input because the count is stable after every branch halts. -/
@[expose] def _root_.Turing.MultiTapeCTM.CountsInLogSpace {k : ℕ} {State : Type}
    (M : MultiTapeCTM k Bool State) (enc : α ↪ List Bool) (f : α → ℕ) : Prop :=
  ∃ c : ℕ, ∀ a,
    M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.HaltsWithin t (Cfg.init M.initial (enc a)) ∧
        f a = M.acceptCount t (Cfg.init M.initial (enc a))

/-- The accepting branch counts of finite logspace counting machines. -/
@[expose] def SharpL (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeCTM k Bool State),
    M.CountsInLogSpace enc f}

/-- Unambiguous logarithmic space. There is one accepting branch on members and none on
nonmembers. -/
@[expose] def UL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- An unambiguous logspace witness yields an NL witness by forgetting transition
multiplicity. Its accepting count is positive exactly when the resulting machine accepts. -/
theorem UL_subset_NL {enc : α ↪ List Bool} : UL enc ⊆ NL enc := by
  rintro A ⟨f, ⟨k, State, hfinite, machine, c, hmachine⟩, _, hA⟩
  refine ⟨k, State, hfinite, machine.toNTM, c, ⟨?_, ?_⟩⟩
  · intro a
    obtain ⟨hspace, t, hclock, hf⟩ := hmachine a
    refine ⟨hspace, (hA a).trans ?_⟩
    rw [hf]
    constructor
    · intro ha
      obtain ⟨p, hp, hh, hout⟩ := (hclock.branchCount_pos_iff (· == [true])).mp ha
      exact ⟨⟨p, hp⟩, hh, beq_iff_eq.mp hout⟩
    · rintro ⟨p, hh, hout⟩
      exact (hclock.branchCount_pos_iff (· == [true])).mpr
        ⟨p.toRunPath, p.head_eq, hh, beq_iff_eq.mpr hout⟩
  · intro a
    obtain ⟨_, t, hclock, _⟩ := hmachine a
    exact ⟨t, fun p hp => hclock.paths_halted p.toRunPath p.head_eq hp⟩

end Cslib.Complexity
