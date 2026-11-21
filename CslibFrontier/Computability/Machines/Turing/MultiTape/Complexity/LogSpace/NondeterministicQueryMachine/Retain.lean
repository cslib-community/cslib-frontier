/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine

/-!
# Query machines with immutable context

A fixed machine can run a family of query machines by carrying the family index in its
state. The index is available to every transition and survives all replays.

## Main results

* `Turing.NondeterministicQueryMachine.replay_retain`: replay with the same input and selectors.
* `Turing.NondeterministicQueryMachine.firstHalting_retain`: the same strict first halt.
-/

public section

namespace Turing.NondeterministicQueryMachine

variable {κ σ ρ : Type*}

/-- Select a query machine using the context stored alongside its state.
The equivalence lets a caller retain its own named state fields. -/
@[expose] def retain (e : ρ ≃ κ × σ) (machine : κ → NondeterministicQueryMachine σ)
    (context : κ) : NondeterministicQueryMachine ρ where
  init := e.symm (context, (machine context).init)
  query s := (machine (e s).1).query (e s).2
  next p := e.symm ((e p.1).1, (machine (e p.1).1).next ((e p.1).2, p.2))
  halted s := (machine (e s).1).halted (e s).2
  accept s := (machine (e s).1).accept (e s).2

/-- Re-entry can change the retained context as well as the inner initial state. -/
theorem retain_withInit (e : ρ ≃ κ × σ) (machine : κ → NondeterministicQueryMachine σ)
    (context next : κ) (s : σ) :
    (retain e machine context).withInit (e.symm (next, s)) =
      retain e (fun k => (machine k).withInit s) next :=
  rfl

private theorem step_retain (e : ρ ≃ κ × σ) (machine : κ → NondeterministicQueryMachine σ)
    (context k : κ) (input : List Bool) (s : σ) (choice : Bool) :
    (retain e machine context).step input (e.symm (k, s)) choice =
      e.symm (k, (machine k).step input s choice) := by
  simp only [step, read, retain, Equiv.apply_symm_apply]
  split <;> rfl

/-- The context stays fixed while the selected machine sees the original input and selectors. -/
theorem replay_retain (e : ρ ≃ κ × σ) (machine : κ → NondeterministicQueryMachine σ)
    (context k : κ) (input choices : List Bool) (s : σ) :
    (retain e machine context).replay input choices (e.symm (k, s)) =
      e.symm (k, (machine k).replay input choices s) :=
  List.foldl_hom (fun t => e.symm (k, t)) (step_retain e machine context k input)

/-- Every first-halting selector list is preserved at a retained entry. -/
theorem firstHalting_retain (e : ρ ≃ κ × σ) (machine : κ → NondeterministicQueryMachine σ)
    (context k : κ) (input choices : List Bool) (s : σ) :
    (retain e machine context).FirstHalting input choices (e.symm (k, s)) ↔
      (machine k).FirstHalting input choices s := by
  simp only [FirstHalting, replay_retain]
  simp only [retain, Equiv.apply_symm_apply]

end Turing.NondeterministicQueryMachine
