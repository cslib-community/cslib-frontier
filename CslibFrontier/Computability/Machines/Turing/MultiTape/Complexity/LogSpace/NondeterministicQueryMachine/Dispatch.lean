/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# Query-machine dispatch by entry state

A caller selects one of two callback machines by tagging the entry state. The selected machine
reads the original input and consumes exactly its own selectors. The tag remains fixed so the
caller can decode the final state with the corresponding reply function.
-/

public section

namespace Turing.NondeterministicQueryMachine

variable {σ τ : Type*}
  (left : NondeterministicQueryMachine σ) (right : NondeterministicQueryMachine τ)

/-- Run the callback selected by the entry tag. The default entry is the left machine's initial
state. Re-enter at a right-tagged state to use the right machine. -/
@[expose] def dispatch : NondeterministicQueryMachine (σ ⊕ τ) where
  init := .inl left.init
  query := Sum.elim left.query right.query
  next := fun (s, bit, choice) =>
    s.map (fun q => left.next (q, bit, choice)) (fun q => right.next (q, bit, choice))
  halted := Sum.elim left.halted right.halted
  accept := Sum.elim left.accept right.accept

private theorem step_dispatch (input : List Bool) (choice : Bool) (s : σ ⊕ τ) :
    (left.dispatch right).step input s choice =
      s.map (fun q => left.step input q choice) (fun q => right.step input q choice) := by
  cases s with
  | inl q => cases h : left.halted q <;> simp [dispatch, step, read, h]
  | inr q => cases h : right.halted q <;> simp [dispatch, step, read, h]

/-- Dispatch preserves the entry tag and forwards the entire selector list on the original input. -/
theorem replay_dispatch (input bits : List Bool) (s : σ ⊕ τ) :
    (left.dispatch right).replay input bits s =
      s.map (left.replay input bits) (right.replay input bits) := by
  cases s with
  | inl q =>
    exact List.foldl_hom Sum.inl fun state choice =>
      step_dispatch left right input choice (.inl state)
  | inr q =>
    exact List.foldl_hom Sum.inr fun state choice =>
      step_dispatch left right input choice (.inr state)

/-- The left-tagged dispatch first halts on precisely the left callback's first-halting lists. -/
theorem firstHalting_dispatch_inl (input bits : List Bool) (s : σ) :
    (left.dispatch right).FirstHalting input bits (.inl s) ↔ left.FirstHalting input bits s := by
  simp only [FirstHalting, replay_dispatch]
  rfl

/-- The right-tagged dispatch first halts on precisely the right callback's first-halting lists. -/
theorem firstHalting_dispatch_inr (input bits : List Bool) (s : τ) :
    (left.dispatch right).FirstHalting input bits (.inr s) ↔ right.FirstHalting input bits s := by
  simp only [FirstHalting, replay_dispatch]
  rfl

end Turing.NondeterministicQueryMachine
