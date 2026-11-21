/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting.Predecessor
import Mathlib.Data.Nat.Find

/-!
# Native compilation of predecessor counting with supplied callees

The query caller previously retained its answer only in state. `computingMachine` preserves
its transitions and emits the optional binary count at halt. `compute_of_callees` applies the
existing query-machine compiler to obtain an actual native time/space computation certificate.

The context is fixed for this invocation family, as in `Predecessor.machine`; its complete
encoded word is charged. Callee first-halting, reply correctness, native components, initializer,
reply decoder and all-clock callee-state bounds are explicit premises. The original-input
position costs `log₂ inputLength + 1` independently of the suspended context and callee state.
The returned native time bound is existential and independent of space. No polynomial physical
runtime, uniform runtime-context/input dispatcher, native choice-count correspondence or full
outer controller is asserted; these remain under #6747.
-/

public section
namespace Turing.DoubleCounting.Predecessor
open Cslib.DoubleCounting MultiTapeTM ComputableInSpace

/-- One option tag followed by the binary predecessor count on success. -/
abbrev encCountResult : Option ℕ ↪ List Bool := encOption encNat

/-- Emit the result at a caller halt; active callees never finish the composite. -/
@[expose] def finishResult {τ : Type} : State ⊕ (State × τ) → List Bool
  | .inl q => encCountResult (result q)
  | .inr _ => []

/-- The predecessor routine with result output; all call transitions are unchanged. -/
@[expose] def computingMachine {τ : Type} (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool) : QueryMachine (State ⊕ (State × τ)) :=
  { machine ctx N start answer with finish := finishResult }

private theorem finishResult_inSpace {τ : Type} (encT : τ ↪ List Bool) :
    ComputableInSpace (finishResult (τ := τ)) (encMachineState encT) encBits
      (fun q => (encMachineState encT q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encState)).inO_one
  have hresult := budget_ite (encState_rejected_budget hid)
    (budget_const (encB := encCountResult) none (.refl _))
    (budget_optionSome (encState_count_budget hid))
  have hleft : ComputableInSpace (fun q => encCountResult (result q)) encState encBits
      (fun q => (encState q).length) := hresult.of_enc_eq fun _ => rfl
  exact (sumElim hleft (budget_const [] (.refl _))).of_enc_eq fun q => by cases q <;> rfl

/-- Concatenating actual calls retains the per-call bound at every clock of the whole run.
Only first-halting callee segments need the supplied bound. -/
theorem Returns.exists_run_encoding_le {τ : Type} (encT : τ ↪ List Bool)
    {ctx : Context} {N : QueryMachine τ} {start : State → τ} {answer : τ → Option Bool}
    {w : List Bool} {q : State} (h : Returns ctx N start answer w q) (D : ℕ)
    (hc : ∀ p : State, p.context = ctx → Bounded p → halted p = false → ∀ T,
      (∀ i < T, N.halted (N.runFrom w (start p) i) = false) →
      N.halted (N.runFrom w (start p) T) = true →
      ∀ i ≤ T, (encT (N.runFrom w (start p) i)).length ≤ D) :
    ∃ T, (machine ctx N start answer).runFrom w (.inl (Predecessor.initial ctx)) T = .inl q ∧
      ∀ i ≤ T,
        (encMachineState encT
          ((machine ctx N start answer).runFrom w (.inl (Predecessor.initial ctx)) i)).length ≤
          4 * (encContext ctx).length + 8 * (Nat.log2 ctx.size + 1) + D + 16 := by
  induction h with
  | initial =>
    refine ⟨0, rfl, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rw [QueryMachine.runFrom_zero, QueryMachine.withCalls_encoding_inl_length]
    have h := length_encState_le (Returns.bounded (Returns.initial (ctx := ctx) (N := N)
      (start := start) (answer := answer) (w := w)))
    change (encState (Predecessor.initial ctx)).length ≤ _ at h
    change (encState (Predecessor.initial ctx)).length + 1 ≤ _
    change (encState (Predecessor.initial ctx)).length ≤
      2 * (encContext ctx).length + 4 * (Nat.log2 ctx.size + 1) + 7 at h
    omega
  | @call p hp hlive T hpre hhalt ih =>
    obtain ⟨U, hU, hUB⟩ := ih
    have hcall := runFrom_call_encoding_le encT ctx N start answer w p hp.bounded hlive T D
      hpre hhalt (hc p hp.context_eq hp.bounded hlive T hpre hhalt)
    rw [hp.context_eq] at hcall
    refine ⟨U + (T + 2), ?_, ?_⟩
    · rw [QueryMachine.runFrom_add, hU, runFrom_call ctx N start answer w p hlive T hpre hhalt]
    · apply QueryMachine.runFrom_add_encoding_le (encMachineState encT)
        (.inl (Predecessor.initial ctx)) hUB
      simpa only [hU] using hcall

/-- Compile the actual predecessor routine to a native computation, for a fixed explicit
context and supplied same-input callees. Space charges original-input positions and the whole
suspended caller/callee frame. Native time is independent and existential; no runtime polynomial
or native genuine-choice counting correspondence is inferred. -/
theorem compute_of_callees {α τ : Type} {n : ℕ} (enc : α ↪ List Bool)
    (encT : τ ↪ List Bool) (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool)
    (edge : α → Fin n → Fin n → Option Bool) (member : α → Fin n → Option Bool)
    (v : Fin n) (hsize : ctx.size = n)
    (hq : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hn : ComputableInSpace N.next (QueryMachine.encStateRead encT) encT
      (fun p => (QueryMachine.encStateRead encT p).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length))
    (ha : ComputableInSpace answer encT (encOption encBool) (fun t => (encT t).length))
    (D S : α → ℕ)
    (ht : ∀ a p, p.context = ctx → Bounded p → halted p = false →
      ∃ T, (∀ i < T, N.halted (N.runFrom (enc a) (start p) i) = false) ∧
        N.halted (N.runFrom (enc a) (start p) T) = true)
    (hb : ∀ a p, p.context = ctx → Bounded p → halted p = false → ∀ T,
      (∀ i < T, N.halted (N.runFrom (enc a) (start p) i) = false) →
      N.halted (N.runFrom (enc a) (start p) T) = true →
      ∀ i ≤ T, (encT (N.runFrom (enc a) (start p) i)).length ≤ D a)
    (hc : ∀ a p, p.context = ctx → ∀ hi : p.cursor < n, ∀ T,
      (∀ i < T, N.halted (N.runFrom (enc a) (start p) i) = false) →
      N.halted (N.runFrom (enc a) (start p) T) = true →
      answer (N.runFrom (enc a) (start p) T) =
        if p.memberPhase then member a ⟨p.cursor, hi⟩ else edge a ⟨p.cursor, hi⟩ v)
    (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hframe : ∀ a, 4 * (encContext ctx).length +
      8 * (Nat.log2 ctx.size + 1) + D a + 16 ≤ S a) :
    ∃ time c, ComputableInTimeAndSpace
      (fun a => countPredecessors (edge a) (member a) v) enc encCountResult time
      (fun a => c * S a) := by
  classical
  let Q := computingMachine ctx N start answer
  have cert (a : α) : ∃ T q, Returns ctx N start answer (enc a) q ∧ halted q = true ∧
      Q.run (enc a) T = .inl q ∧
      ∀ i ≤ T, (encMachineState encT (Q.run (enc a) i)).length ≤ S a := by
    obtain ⟨q, htrace, hstop⟩ := exists_stopped_returns ctx N start answer (enc a) (ht a)
    obtain ⟨T, hT, hB⟩ := htrace.exists_run_encoding_le encT (D a) (hb a)
    refine ⟨T, q, htrace, hstop, hT, ?_⟩
    intro i hi
    exact (hB i hi).trans (hframe a)
  have stops (a : α) : ∃ T, Q.halted (Q.run (enc a) T) = true := by
    obtain ⟨T, q, _, hstop, hT, _⟩ := cert a
    exact ⟨T, by rw [hT]; exact hstop⟩
  let time (a : α) := Nat.find (stops a)
  have hhalt (a : α) : Q.halted (Q.run (enc a) (time a)) = true := Nat.find_spec (stops a)
  have hpre (a : α) (i : ℕ) (hi : i < time a) : Q.halted (Q.run (enc a) i) = false := by
    cases h : Q.halted (Q.run (enc a) i) with
    | false => rfl
    | true => exact False.elim (Nat.find_min (stops a) hi h)
  have hemit (p : (State ⊕ (State × τ)) × Option Bool) : Q.emit p = [] := by
    rcases p with ⟨q | ⟨q, t⟩, b⟩
    · cases h : request start q <;>
        simp [Q, computingMachine, machine, QueryMachine.withCalls, h, caller]
    · rfl
  have hf (a : α) : encCountResult (countPredecessors (edge a) (member a) v) =
      Q.output (enc a) (time a) := by
    obtain ⟨T, q, htrace, hstop, hT, _⟩ := cert a
    have hQT : Q.halted (Q.run (enc a) T) = true := by rw [hT]; exact hstop
    have hle : time a ≤ T := Nat.find_min' (stops a) hQT
    have hstate : Q.run (enc a) (time a) = .inl q :=
      (Q.run_eq_of_le (enc a) (hhalt a) hle).symm.trans hT
    have hresult := result_of_returns (edge a) (member a) v hsize htrace hstop (hc a)
    rw [Q.output_eq_finish_of_emit_nil (enc a) hemit, hstate]
    exact congrArg encCountResult hresult.symm
  apply Q.computableInSpace (machine_query_inSpace encT ctx N start answer hq hs)
    (machine_next_inSpace encT ctx N start answer hn hh hs ha)
    (machine_emit_inSpace encT ctx N start answer hs)
    (machine_halted_inSpace encT ctx N start answer) (finishResult_inSpace encT)
    time hhalt hpre hf S hlog
  refine ⟨1, ?_⟩
  intro a i hi
  obtain ⟨T, q, _, hstop, hT, hB⟩ := cert a
  have hQT : Q.halted (Q.run (enc a) T) = true := by rw [hT]; exact hstop
  have hle : time a ≤ T := Nat.find_min' (stops a) hQT
  simpa only [Nat.one_mul] using hB i (hi.trans hle)

end Turing.DoubleCounting.Predecessor
