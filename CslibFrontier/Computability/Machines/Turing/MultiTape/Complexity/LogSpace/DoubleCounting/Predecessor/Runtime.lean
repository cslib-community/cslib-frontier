/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Offset
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FramePrefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Runtime predecessor context and original-input query transport

`load_inSpace` supplies one native initializer for all runtime contexts, using only the framed
context prefix as workspace. `executor_runFrom` transports every clock of the actual predecessor
machine to the unchanged payload suffix, including absent reads, rejection and suspended calls.
The offset is retained runtime data, not a machine selected for a fixed context.

The shared `QueryMachine.withOffset_runFrom_encoding_le` charges the binary offset over the supplied
inner all-clock bound. `compute_of_callees` compiles the initializer and executor together,
charging the original input position and the suspended caller and callee states. The supplied
callees have native component and first-halting contracts, and the resulting time bound is
existential and independent of workspace.
-/

public section
namespace Turing.DoubleCounting.Predecessor.Runtime
open MultiTapeTM ComputableInSpace Cslib.DoubleCounting
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
  exact (encLocated_mk_budget State encState hc.frameLength
    (budget_comp_linear initial_inSpace hc)).of_enc_eq fun _ => by
      simp only [load, length_frame]

/-- Dropping the loaded header leaves exactly the unchanged callback input word. -/
theorem drop_payload (x : Input) : (encInput x).drop (load x).offset = x.payload := by
  have hoff : (load x).offset = (frame (encContext x.context)).length := by simp [load]
  rw [hoff]
  simp [encInput_apply, encInputFields, encPair_apply, encBits_apply]

/-- One fixed predecessor executor. Its dummy initial context is unused by `runFrom`:
`entry` supplies the runtime context as data. -/
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

private theorem entry_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace (entry τ) encInput
      (encLocated (State ⊕ (State × τ)) (encMachineState encT))
      (fun x => (encContext x.context).length + 1) := by
  have hi := QueryMachine.encLocated_inner_budget State encState load_inSpace
  exact encLocated_mk_budget _ _
    (QueryMachine.encLocated_offset_budget State encState load_inSpace)
    (budget_comp_linear (of_inO (ComputableInO.inl encState (encPair encState encT))) hi)

/-- Compile a predecessor count with context in the framed input and supplied native callees.
The callback semantics and callee state bounds are measured on the original payload. The native
machine includes the complete frame and original-input position in its workspace budget. -/
theorem compute_of_callees {α τ : Type} {n : α → ℕ} (enc : α ↪ List Bool)
    (input : α → Input) (layout : ∀ a, enc a = encInput (input a))
    (encT : τ ↪ List Bool) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool)
    (edge : (a : α) → Fin (n a) → Fin (n a) → Option Bool)
    (member : (a : α) → Fin (n a) → Option Bool)
    (v : (a : α) → Fin (n a)) (hsize : ∀ a, (input a).context.size = n a)
    (hq : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hn : ComputableInSpace N.next (QueryMachine.encStateRead encT) encT
      (fun p => (QueryMachine.encStateRead encT p).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length))
    (ha : ComputableInSpace answer encT (encOption encBool) (fun t => (encT t).length))
    (D S : α → ℕ)
    (ht : ∀ a p, p.context = (input a).context → Bounded p → halted p = false →
      ∃ T, (∀ i < T, N.halted (N.runFrom (input a).payload (start p) i) = false) ∧
        N.halted (N.runFrom (input a).payload (start p) T) = true)
    (hb : ∀ a p, p.context = (input a).context → Bounded p → halted p = false → ∀ T,
      (∀ i < T, N.halted (N.runFrom (input a).payload (start p) i) = false) →
      N.halted (N.runFrom (input a).payload (start p) T) = true →
      ∀ i ≤ T, (encT (N.runFrom (input a).payload (start p) i)).length ≤ D a)
    (hc : ∀ a p, p.context = (input a).context → ∀ hi : p.cursor < n a, ∀ T,
      (∀ i < T, N.halted (N.runFrom (input a).payload (start p) i) = false) →
      N.halted (N.runFrom (input a).payload (start p) T) = true →
      answer (N.runFrom (input a).payload (start p) T) =
        if p.memberPhase then member a ⟨p.cursor, hi⟩ else edge a ⟨p.cursor, hi⟩ (v a))
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hframe : ∀ a, 2 * (encNat (load (input a)).offset).length + 1 +
      (4 * (encContext (input a).context).length +
        8 * (Nat.log2 (input a).context.size + 1) + D a + 16) ≤ S a) :
    ∃ time c, ComputableInTimeAndSpace
      (fun a => countPredecessors (edge a) (member a) (v a)) enc encCountResult time
      (fun a => c * S a) := by
  classical
  let dummy : Context := ⟨0, 0, 0, 0, ⟨0, 0⟩⟩
  let Q := computingMachine dummy N start answer
  let E := executor N start answer
  let encE := encLocated (State ⊕ (State × τ)) (encMachineState encT)
  let run (a : α) := E.runFrom (enc a) (entry τ (input a))
  have hemit (p) : E.emit p = [] :=
    computingMachine_emit_eq_nil dummy N start answer (p.1.inner, p.2)
  have cert (a : α) : ∃ T, E.halted (run a T) = true ∧
      (∀ i < T, E.halted (run a i) = false) ∧
      encCountResult (countPredecessors (edge a) (member a) (v a)) =
        E.outputFrom (enc a) (entry τ (input a)) T ∧
      ∀ i ≤ T, (encE (run a i)).length ≤ S a := by
    obtain ⟨q, htrace, hstop⟩ := exists_stopped_returns _ _ _ _ _ (ht a)
    obtain ⟨T, hhalt, hpre, hT, hB⟩ :=
      htrace.exists_firstHalt_encoding_le encT hstop (D a) (hb a)
    let inner := computingMachine (input a).context N start answer
    have transport (i : ℕ) :
        run a i = ⟨(load (input a)).offset, inner.run (input a).payload i⟩ := by
      unfold run E
      rw [layout, executor_runFrom]
      rfl
    refine ⟨T, by rw [transport]; exact hhalt,
      fun i hi => by rw [transport]; exact hpre i hi, ?_, ?_⟩
    · rw [E.outputFrom_eq_finish_of_emit_nil _ hemit]
      change _ = E.finish (run a T)
      rw [transport, hT]
      exact congrArg encCountResult
        (result_of_returns (edge a) (member a) (v a) (hsize a) htrace hstop (hc a)).symm
    · have htransport := inner.withOffset_runFrom_encoding_le (encMachineState encT)
        (encInput (input a)) (load (input a)).offset (.inl (initial (input a).context))
        (4 * (encContext (input a).context).length +
          8 * (Nat.log2 (input a).context.size + 1) + D a + 16) T
        (by rw [drop_payload]; exact hB)
      intro i hi
      have h := htransport i hi
      rw [← layout a] at h
      exact h.trans (hframe a)
  choose clock hhalt hpre hf hB using cert
  have hinit := (entry_inSpace encT).of_encIn_eq input layout
  apply E.computableInSpaceFrom
    (Q.withOffset_query_inSpace _ (machine_query_inSpace encT dummy N start answer hq hs))
    (Q.withOffset_next_inSpace _ (machine_next_inSpace encT dummy N start answer hn hh hs ha))
    (Q.withOffset_emit_inSpace _ (machine_emit_inSpace encT dummy N start answer hs))
    (Q.withOffset_halted_inSpace _ (machine_halted_inSpace encT dummy N start answer))
    (Q.withOffset_finish_inSpace _ (finishResult_inSpace encT))
    clock S (hinit.mono_le (fun a => by have h := hframe a; omega)) hhalt hpre hf hlog
  exact ⟨1, by simpa only [Nat.one_mul] using hB⟩

end Turing.DoubleCounting.Predecessor.Runtime
