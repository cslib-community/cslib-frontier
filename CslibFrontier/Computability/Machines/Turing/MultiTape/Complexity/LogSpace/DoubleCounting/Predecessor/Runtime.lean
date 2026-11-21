/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Runtime predecessor context and original-input query transport

This original initializer/dispatch bridge is not a uniform native predecessor computation.
`load_inSpace` supplies one native initializer for all runtime contexts, using only the framed
context prefix as workspace. `executor_runFrom` transports every clock of the actual predecessor
machine to the unchanged payload suffix, including absent reads, rejection and suspended calls.
The offset is retained runtime data, not a machine selected for a fixed context.

The shared `QueryMachine.withOffset_runFrom_encoding_le` charges the binary offset over the supplied
inner all-clock bound. The latter must already include suspended caller and callee states.
Initializer time is existential and independent of its space bound; payload length is not
charged as workspace. Composing the initializer with execution in one native machine, including
retaining/resetting access to its original input and compiling the transported components, remains
open in #6747. No callback's physical runtime or workspace is inferred from query transport.
-/

public section
namespace Turing.DoubleCounting.Predecessor.Runtime
open MultiTapeTM ComputableInSpace
open QueryMachine (Located encLocated encLocated_mk_budget)

/-- A runtime controller header followed by the original callback input word. -/
structure Input where
  /-- Size, source, target, radius and expected tally. -/
  context : Context
  /-- The unchanged word on which adjacency and membership callees operate. -/
  payload : List Bool

/-- Framed binary `encContext`, then raw payload bits without additional framing. -/
enc_structure encInput : Input where context : encContext, payload : encBits

/-- Load all runtime arguments and the exact payload offset; no payload is retained. -/
@[expose] def load (x : Input) : Located State :=
  ⟨2 * (encContext x.context).length + 1, initial x.context⟩

/-- One native initializer, with workspace linear in the binary header length independently
of payload length. This certifies initialization, not subsequent native execution. -/
theorem load_inSpace : ComputableInSpace load encInput (encLocated State encState)
    (fun x => (encContext x.context).length + 1) := by
  have hc : ComputableInSpace Input.context encInput encContext
      (fun x => (encContext x.context).length + 1) :=
    (ComputableInSpace.framedPrefix Input.context encInput encContext Input.payload
      (fun x => by simp [encInput_apply, encInputFields])).mono_le (fun _ => by omega)
  have hb : ComputableInSpace (fun x : Input => encContext x.context) encInput encBits
      (fun x => (encContext x.context).length + 1) := hc.of_enc_eq (fun _ => rfl)
  have hlen := (of_inO ComputableInO.lengthNat).weaken
    (show (fun w : List Bool => w.length) ≼ fun w => (encBits w).length from
      .of_le_linear 1 1 fun w => by simp [encBits_apply])
  have hl := budget_comp_linear hlen hb
  have one : ComputableInSpace (fun _ : Input => 1) encInput encNat
      (fun x => (encContext x.context).length + 1) :=
    (constZero 1).weaken (.of_le fun _ => by omega)
  exact (encLocated_mk_budget State encState (budget_natAdd (budget_natAdd hl hl) one)
    (budget_comp_linear initial_inSpace hc)).of_enc_eq fun x => by
      apply congrArg (encLocated State encState)
      simp only [load]
      congr 1
      omega

/-- Dropping the loaded header leaves exactly the unchanged callback input word. -/
theorem drop_payload (x : Input) : (encInput x).drop (load x).offset = x.payload := by
  have hoff : (load x).offset = (frame (encContext x.context)).length := by simp [load]
  rw [hoff]
  simp [encInput_apply, encInputFields, encPair_apply, encBits_apply]

/-- One fixed predecessor executor. Its dummy initial context is unused by `runFrom`:
`entry` supplies the runtime context as data. This is a query machine, not a compiled native
loader/executor composition. -/
@[expose] def executor {τ : Type} (N : QueryMachine τ) (start : State → τ)
    (answer : τ → Option Bool) : QueryMachine (Located (State ⊕ (State × τ))) :=
  (computingMachine ⟨0, 0, 0, 0, ⟨0, 0⟩⟩ N start answer).withOffset

/-- Initial query state using the runtime-loaded context and payload offset. -/
@[expose] def entry (τ : Type) (x : Input) : Located (State ⊕ (State × τ)) :=
  ⟨(load x).offset, .inl (load x).inner⟩

/-- One fixed query executor agrees with the actual predecessor loop for every runtime context
and every clock. All callback reads, including suspended-call reads, refer to the payload. -/
theorem executor_runFrom {τ : Type} (N : QueryMachine τ) (start : State → τ)
    (answer : τ → Option Bool) (x : Input) (t : ℕ) :
    (executor N start answer).runFrom (encInput x) (entry τ x) t =
      ⟨(load x).offset, (computingMachine x.context N start answer).runFrom x.payload
        (.inl (initial x.context)) t⟩ := by
  change (computingMachine ⟨0, 0, 0, 0, ⟨0, 0⟩⟩ N start answer).withOffset.runFrom
    (encInput x) ⟨(load x).offset, .inl (initial x.context)⟩ t = _
  rw [QueryMachine.withOffset_runFrom, drop_payload]
  rfl

end Turing.DoubleCounting.Predecessor.Runtime
