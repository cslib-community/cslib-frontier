/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Dispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Routines
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases

/-!
# Workspace for query-machine dispatch

The step input encodes a framed tagged callback state followed by the shared optional read bit
and selector. Encoded sum case analysis forwards that pair to the selected step and restores the
same tag on its output.
-/

public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM ComputableInSpace

/-- Linear-space callback steps give a linear-space dispatched step with the same read and
selector encoding. -/
theorem dispatch_next_inSpace {σ τ : Type}
    (left : NondeterministicQueryMachine σ) (right : NondeterministicQueryMachine τ)
    (encL : σ ↪ List Bool) (encR : τ ↪ List Bool)
    (hleft : ComputableInSpace left.next (encPair encL encReadChoice) encL
      fun p => (encPair encL encReadChoice p).length)
    (hright : ComputableInSpace right.next (encPair encR encReadChoice) encR
      fun p => (encPair encR encReadChoice p).length) :
    ComputableInSpace (left.dispatch right).next (encPair (encSum encL encR) encReadChoice)
      (encSum encL encR) fun p => (encPair (encSum encL encR) encReadChoice p).length := by
  have hinl := of_inO (ComputableInO.inl encL encR)
  have hinr := of_inO (ComputableInO.inr encL encR)
  refine (sumElimFst (budget_comp_linear hinl hleft) (budget_comp_linear hinr hright)).of_enc_eq ?_
  rintro ⟨a | b, read, choice⟩ <;> rfl

end Turing.NondeterministicQueryMachine
