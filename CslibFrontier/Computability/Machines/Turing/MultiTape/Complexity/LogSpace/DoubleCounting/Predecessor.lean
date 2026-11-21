/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.DoubleCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Same-input predecessor counting calls

A bounded scalar cursor scans predecessors of one target. The caller retains the graph size,
source, target, radius and expected tally across every adjacency or membership call. `memberPhase`
distinguishes the two requests. A callee returns `Option Bool`: `none` rejects, and `some false`
continues. The only predecessor dispatch is `Cslib.DoubleCounting.predecessorStep`, interpreted
with a suspended membership request. No predecessor list is stored.

The scalar cursor is stored in binary and is a finite index through the invariant
`count ≤ cursor ≤ size`; the endpoint `cursor = size` halts. The request initializer receives
all context as explicit state and is responsible for routing edge/member requests to its
same-input callee. Its initialization and reply extraction costs are explicit hypotheses.

## Main results

* `advance_bounded`: count never exceeds fully tested indices, and the cursor stays in range.
* `result_of_returns`: finite actual call traces agree with `countPredecessors`, including
  rejection, provided the phase-selected callee agrees with the supplied callbacks.
* `exists_stopped_returns`: termination of each requested callee implies a finite stopped
  query-machine call trace, using a decreasing finite phase measure.
* `runFrom_call_encoding_le`: every clock of a call, including return after rejection, charges
  at most `4 * contextBits + 8 * (log₂ size + 1) + calleeBits + 16` encoded bits.

`initial_inSpace`, `advance_inSpace` and the five `machine_*_inSpace` component certificates
charge caller arithmetic, initialization, callee dispatch and reply extraction. One supplied
same-input callee/router services both request phases; its contracts remain explicit.

This is a query-machine component and per-call simulation/resource interface. Native genuine
choice/first-halting counting composition and the whole outer controller remain open in #6747.
It does not certify the supplied callbacks' physical time or space without their certificates.
-/

public section
namespace Turing.DoubleCounting.Predecessor
open Cslib.DoubleCounting MultiTapeTM ComputableInSpace

/-- Immutable context retained by the predecessor caller. -/
structure Context where
  /-- Number of vertices; the cursor ranges from zero through this endpoint. -/
  size : ℕ
  /-- Source supplied to the membership routine. -/
  source : ℕ
  /-- Target whose incoming predecessors are tested. -/
  target : ℕ
  /-- Membership radius. -/
  radius : ℕ
  /-- Current-round count and distance sum supplied to membership. -/
  expected : Tally

/-- Live scalar registers, including the pending call phase and rejection status. -/
structure State where
  /-- All original callback arguments are explicit retained data. -/
  context : Context
  /-- Number of fully tested predecessors, or the current predecessor in a membership call. -/
  cursor : ℕ
  /-- Count of qualifying predecessors among completed tests. -/
  count : ℕ
  /-- True only after a positive adjacency answer, while membership is pending. -/
  memberPhase : Bool
  /-- A rejected callee terminates the caller and preserves its partial count. -/
  rejected : Bool

/-- Binary size, source, target, radius and binary expected tally, framed in declaration order. -/
enc_structure encContext : Context where
  size : encNat, source : encNat, target : encNat, radius : encNat, expected : encTally

/-- Framed context, binary cursor and count, then phase and rejection bits. -/
enc_structure encState : State where
  context : encContext, cursor : encNat, count : encNat, memberPhase : encBool, rejected : encBool

/-- A framed caller followed by an optional Boolean return value. -/
abbrev encAdvance := encPair encState (encOption encBool)

/-- Start before the first adjacency query. -/
@[expose] def initial (ctx : Context) : State := ⟨ctx, 0, 0, false, false⟩

/-- The rejection flag and finite cursor endpoint are the only stopping conditions. -/
@[expose] def halted (q : State) : Bool := q.rejected || decide (q.context.size ≤ q.cursor)

/-- Observe the original handler after one reply; an exception requests membership rather
than rejecting. Rejection is carried separately by the optional callee answer. -/
@[expose] def observe (q : State) (hit : Bool) : Except Unit ℕ :=
  predecessorStep (fun _ _ => pure (if q.memberPhase then true else hit))
    (fun _ => if q.memberPhase then pure hit else .error ()) q.context.target q.count q.cursor

/-- Apply one returned callback value, preserving the entire immutable context. -/
@[expose] def advance (q : State) (reply : Option Bool) : State :=
  match reply with
  | none => { q with rejected := true }
  | some hit => match observe q hit with
    | .error _ => { q with memberPhase := true }
    | .ok c => { q with cursor := q.cursor + 1, count := c, memberPhase := false }

/-- Rejection has no count; a successful zero or tied count is retained distinctly. -/
@[expose] def result (q : State) : Option ℕ := if q.rejected then none else some q.count

/-- The caller itself reads no input and emits no word; results stay in its final state. -/
@[expose] def caller (ctx : Context) : QueryMachine State where
  init := initial ctx
  query _ := 0
  next p := p.1
  emit _ := []
  halted := halted
  finish _ := []

/-- Initialize exactly one active adjacency/member callee using all explicit arguments. -/
@[expose] def request {τ : Type} (start : State → τ) (q : State) : Option τ :=
  if halted q then none else some (start q)

/-- The same-input callee's final state supplies a Boolean answer or rejection. -/
@[expose] def resume {τ : Type} (answer : τ → Option Bool) (q : State) (t : τ) : State :=
  advance q (answer t)

/-- Predecessor counting via actual same-input calls, with one suspended caller and one callee. -/
@[expose] def machine {τ : Type} (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool) :=
  (caller ctx).withCalls N (request start) (resume answer)

/-- A tagged active caller, or its framed suspended state followed by the callee state. -/
abbrev encMachineState {τ : Type} (encT : τ ↪ List Bool) :=
  QueryMachine.encWithCalls encState encT

/-- Both numeric loop registers stay in their finite ranges, independently of reply truth. -/
def Bounded (q : State) : Prop := q.count ≤ q.cursor ∧ q.cursor ≤ q.context.size

/-- Every reply, including rejection and ties, preserves the bounded scalar invariant. -/
theorem advance_bounded {q : State} (hq : Bounded q) (hlive : halted q = false)
    (reply : Option Bool) : Bounded (advance q reply) := by
  obtain ⟨hc, hi⟩ := hq
  have hlt : q.cursor < q.context.size := by
    simp only [halted, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hlive
    exact hlive.2
  cases reply with
  | none => exact ⟨hc, hi⟩
  | some hit =>
    cases hp : q.memberPhase <;> cases hit <;>
      simp [Bounded, advance, observe, predecessorStep, hp, pure, bind,
        Except.pure, Except.bind] <;> omega

/-- Return preserves the callback context, including rejected returns. -/
theorem advance_context (q : State) (reply : Option Bool) :
    (advance q reply).context = q.context := by
  cases reply with
  | none => rfl
  | some hit => cases h : observe q hit <;> simp only [advance, h]

/-- Execute the unprocessed finite-index suffix using the actual predecessor handler. -/
private def suffix {n : ℕ} (edge : Fin n → Fin n → Option Bool)
    (member : Fin n → Option Bool) (v : Fin n) (c i : ℕ) : Option ℕ :=
  Fin.foldlM (n - i) (fun c u =>
    predecessorStep edge member v c ⟨i + u.val, by have := u.isLt; omega⟩) c

/-- Remaining semantics of the original finite fold. In the membership phase its already
positive edge test is resumed using the same handler; a rejected caller has no result. -/
private def remaining {n : ℕ} (edge : Fin n → Fin n → Option Bool)
    (member : Fin n → Option Bool) (v : Fin n) (q : State) : Option ℕ :=
  if q.rejected then none else
  if q.memberPhase then
    if h : q.cursor < n then do
      let c ← predecessorStep (fun _ _ => some true) member v q.count ⟨q.cursor, h⟩
      suffix edge member v c (q.cursor + 1)
    else some q.count
  else suffix edge member v q.count q.cursor

/-- Initial remaining semantics is precisely the existing `countPredecessors`. -/
private theorem remaining_initial {n : ℕ} (edge : Fin n → Fin n → Option Bool)
    (member : Fin n → Option Bool) (v : Fin n) (ctx : Context) :
    remaining edge member v (initial ctx) = countPredecessors edge member v := by
  simp only [remaining, initial, Bool.false_eq_true, ↓reduceIte, suffix, Nat.sub_zero,
    Nat.zero_add, countPredecessors]

private theorem loop_step {n : ℕ} (edge : Fin n → Fin n → Option Bool)
    (member : Fin n → Option Bool) (v : Fin n) (c i : ℕ) (hi : i < n) :
    suffix edge member v c i = (do
      let c' ← predecessorStep edge member v c ⟨i, hi⟩
      suffix edge member v c' (i + 1)) := by
  unfold suffix
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  conv_lhs => simp only [hn, Fin.foldlM_succ]
  congr 1
  funext c'
  congr 1
  funext a u
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_succ]
  omega

/-- Exact local simulation of the original fold, for either phase and for rejecting replies.
The caller's finite index selects the callback whose return is being simulated. -/
private theorem remaining_advance {n : ℕ} (edge : Fin n → Fin n → Option Bool)
    (member : Fin n → Option Bool) (v : Fin n) (q : State)
    (hi : q.cursor < n) (hr : q.rejected = false) (reply : Option Bool)
    (hreply : reply = if q.memberPhase then member ⟨q.cursor, hi⟩
      else edge ⟨q.cursor, hi⟩ v) :
    remaining edge member v (advance q reply) = remaining edge member v q := by
  cases hp : q.memberPhase with
  | false =>
    have he : edge ⟨q.cursor, hi⟩ v = reply := by simpa [hp] using hreply.symm
    conv_rhs => simp only [remaining, hr, hp, Bool.false_eq_true, ↓reduceIte]
    rw [loop_step edge member v q.count q.cursor hi]
    cases reply with
    | none => simp [remaining, advance, predecessorStep, he]
    | some hit => cases hit <;>
      simp [remaining, advance, observe, predecessorStep, hp, hr, he, hi,
        pure, bind, Except.pure, Except.bind]
  | true =>
    have hm : member ⟨q.cursor, hi⟩ = reply := by simpa [hp] using hreply.symm
    cases reply with
    | none => simp [remaining, advance, predecessorStep, hp, hr, hi, hm]
    | some hit => cases hit <;>
      simp [remaining, advance, observe, predecessorStep, hp, hr, hi, hm,
        pure, bind, Except.pure, Except.bind]

/-- Binary caller length, charging the complete context and both bounded numeric registers. -/
theorem length_encState_le {q : State} (hq : Bounded q) :
    (encState q).length ≤ 2 * (encContext q.context).length +
      4 * (Nat.log2 q.context.size + 1) + 7 := by
  have hc := length_encNat_le_log2 (hq.1.trans hq.2)
  have hi := length_encNat_le_log2 hq.2
  simp only [encState_apply, encStateFields, length_encPair, encBool_apply,
    List.length_singleton]
  omega

/-- Uniform binary initialization copies only the explicit context and adds zero registers. -/
theorem initial_inSpace : ComputableInSpace initial encContext encState
    (fun ctx => (encContext ctx).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encContext)).inO_one
  have zero := budget_const (encIn := encContext) (encB := encNat) 0 (.refl _)
  have no := budget_const (encIn := encContext) (encB := encBool) false (.refl _)
  exact (encState_mk_budget hid zero zero no no).of_enc_eq fun _ => rfl

/-- The scalar resume computation uses linear workspace in its binary caller/reply encoding. -/
theorem advance_inSpace : ComputableInSpace (fun p : State × Option Bool => advance p.1 p.2)
    encAdvance encState (fun p => (encAdvance p).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encState)).inO_one
  have hctx := encState_context_budget hid
  have hi := encState_cursor_budget hid
  have hc := encState_count_budget hid
  have hp := encState_memberPhase_budget hid
  have hr := encState_rejected_budget hid
  have htrue := budget_const (encIn := encState) (encB := encBool) true (.refl _)
  have hnone := encState_mk_budget hctx hi hc hp htrue
  have hs := fst encState encBool
  have hb := snd encState encBool
  have hx := encState_context_budget hs
  have hxI := encState_cursor_budget hs
  have hxC := encState_count_budget hs
  have hxP := encState_memberPhase_budget hs
  have hxR := encState_rejected_budget hs
  have one := budget_const (encIn := encPair encState encBool) (encB := encNat) 1 (.refl _)
  have yes := budget_const (encIn := encPair encState encBool) (encB := encBool) true (.refl _)
  have no := budget_const (encIn := encPair encState encBool) (encB := encBool) false (.refl _)
  have pending := encState_mk_budget hx hxI hxC yes hxR
  have done := encState_mk_budget hx (budget_natAdd hxI one)
    (budget_ite hb (budget_natAdd hxC one) hxC) no hxR
  have skipped := encState_mk_budget hx (budget_natAdd hxI one) hxC no hxR
  refine (optionElimSnd hnone (budget_ite hxP done (budget_ite hb pending skipped))).of_enc_eq ?_
  rintro ⟨q, reply⟩
  cases reply with
  | none => rfl
  | some hit => cases hp : q.memberPhase <;> cases hit <;>
      simp [advance, observe, predecessorStep, hp, pure, bind, Except.pure, Except.bind]

private theorem halted_inSpace : ComputableInSpace halted encState encBool
    (fun q => (encState q).length) := by
  have hid := of_inO (ComputableInDegree.id' (enc := encState)).inO_one
  have hi := encState_cursor_budget hid
  have hn := encContext_size_budget (encState_context_budget hid)
  have hr := encState_rejected_budget hid
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 || p.2)
    (budget_prod hr (budget_natLe hn hi))).of_enc_eq fun _ => rfl

private theorem request_inSpace {τ : Type} (encT : τ ↪ List Bool) (start : State → τ)
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length)) :
    ComputableInSpace (request start) encState (encOption encT)
      (fun q => (encState q).length) := by
  exact (budget_ite halted_inSpace (budget_const none (.refl _)) (budget_optionSome hs)).of_enc_eq
    fun _ => rfl

private theorem resume_inSpace {τ : Type} (encT : τ ↪ List Bool) (answer : τ → Option Bool)
    (ha : ComputableInSpace answer encT (encOption encBool) (fun t => (encT t).length)) :
    ComputableInSpace (fun p : State × τ => resume answer p.1 p.2)
      (encPair encState encT) encState (fun p => (encPair encState encT p).length) :=
  (budget_comp_linear advance_inSpace
    (budget_prod (fst encState encT) (budget_comp_linear ha (snd encState encT)))).of_enc_eq
    fun _ => rfl

/-- Native transition component: caller registers, initializer, callee step/halt, and reply
extraction are charged. This is a component certificate, not first-halting counting composition. -/
theorem machine_next_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool)
    (hn : ComputableInSpace N.next (QueryMachine.encStateRead encT) encT
      (fun p => (QueryMachine.encStateRead encT p).length))
    (hh : ComputableInSpace N.halted encT encBool (fun t => (encT t).length))
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length))
    (ha : ComputableInSpace answer encT (encOption encBool) (fun t => (encT t).length)) :
    ComputableInSpace (machine ctx N start answer).next
      (QueryMachine.encStateRead (encMachineState encT)) (encMachineState encT)
      (fun p => (QueryMachine.encStateRead (encMachineState encT) p).length) :=
  QueryMachine.withCalls_next_inSpace _ _ _ _ _ _ (fst encState (encOption encBool)) hn hh
    (request_inSpace encT start hs) (resume_inSpace encT answer ha)

/-- The active callee reads the original input; request construction has its own certificate. -/
theorem machine_query_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool)
    (hq : ComputableInSpace N.query encT encNat (fun t => (encT t).length))
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length)) :
    ComputableInSpace (machine ctx N start answer).query (encMachineState encT) encNat
      (fun q => (encMachineState encT q).length) :=
  QueryMachine.withCalls_query_inSpace _ _ _ _ _ _ (budget_const 0 (.refl _)) hq
    (request_inSpace encT start hs)

/-- The caller halt test charges the binary cursor comparison and rejection bit. -/
theorem machine_halted_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool) :
    ComputableInSpace (machine ctx N start answer).halted (encMachineState encT) encBool
      (fun q => (encMachineState encT q).length) :=
  QueryMachine.withCalls_halted_inSpace _ _ _ _ _ _ halted_inSpace

/-- Callee output streams are discarded; the caller never emits an intermediate word. -/
theorem machine_emit_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool)
    (hs : ComputableInSpace start encState encT (fun q => (encState q).length)) :
    ComputableInSpace (machine ctx N start answer).emit
      (QueryMachine.encStateRead (encMachineState encT)) encBits
      (fun p => (QueryMachine.encStateRead (encMachineState encT) p).length) :=
  QueryMachine.withCalls_emit_inSpace _ _ _ _ _ _ (budget_const [] (.refl _))
    (request_inSpace encT start hs)

/-- The result remains in the caller state; there is no final output word to accumulate. -/
theorem machine_finish_inSpace {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool) :
    ComputableInSpace (machine ctx N start answer).finish (encMachineState encT) encBits
      (fun q => (encMachineState encT q).length) :=
  QueryMachine.withCalls_finish_inSpace _ _ _ _ _ _ (budget_const [] (.refl _))

/-- A same-input call runs the callee unchanged and resumes with its actual optional answer. -/
theorem runFrom_call {τ : Type} (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool) (w : List Bool) (q : State)
    (hlive : halted q = false) (T : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start q) i) = false)
    (hhalt : N.halted (N.runFrom w (start q) T) = true) :
    (machine ctx N start answer).runFrom w (.inl q) (T + 2) =
      .inl (advance q (answer (N.runFrom w (start q) T))) := by
  apply QueryMachine.withCalls_runFrom_call
  · exact hlive
  · simp [request, hlive]
  · exact hpre
  · exact hhalt

/-- A finite sequence of actual first-halting callee returns. This is proof data, not a list
stored by the machine and not an assertion that every native branch has such a trace. -/
inductive Returns {τ : Type} (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool) (w : List Bool) : State → Prop where
  /-- Initial caller boundary. -/
  | initial : Returns ctx N start answer w (initial ctx)
  /-- Complete one actual same-input call. -/
  | call {q} : Returns ctx N start answer w q → (hlive : halted q = false) → (T : ℕ) →
      (∀ i < T, N.halted (N.runFrom w (start q) i) = false) →
      N.halted (N.runFrom w (start q) T) = true →
      Returns ctx N start answer w (advance q (answer (N.runFrom w (start q) T)))

/-- Every boundary in a finite call trace preserves count ≤ tested indices ≤ size. -/
theorem Returns.bounded {τ : Type} {ctx : Context} {N : QueryMachine τ}
    {start : State → τ} {answer : τ → Option Bool} {w : List Bool} {q : State}
    (h : Returns ctx N start answer w q) : Bounded q := by
  induction h with
  | initial => exact ⟨le_rfl, Nat.zero_le _⟩
  | call _ hlive _ _ _ ih => exact advance_bounded ih hlive _

/-- All immutable callback arguments survive every return, including rejection. -/
theorem Returns.context_eq {τ : Type} {ctx : Context} {N : QueryMachine τ}
    {start : State → τ} {answer : τ → Option Bool} {w : List Bool} {q : State}
    (h : Returns ctx N start answer w q) : q.context = ctx := by
  induction h with
  | initial => rfl
  | call _ _ _ _ _ ih => rw [advance_context]; exact ih

/-- A finite return trace is realized by the actual `withCalls` machine. -/
theorem Returns.exists_run {τ : Type} {ctx : Context} {N : QueryMachine τ}
    {start : State → τ} {answer : τ → Option Bool} {w : List Bool} {q : State}
    (h : Returns ctx N start answer w q) :
    ∃ T, (machine ctx N start answer).runFrom w (.inl (Predecessor.initial ctx)) T = .inl q := by
  induction h with
  | initial => exact ⟨0, rfl⟩
  | @call q h hlive T hpre hhalt ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨S + (T + 2), ?_⟩
    rw [QueryMachine.runFrom_add, hS, runFrom_call ctx N start answer w q hlive T hpre hhalt]

/-- Pending callback phases remaining: two per untested predecessor, minus the completed
edge test while membership is pending. -/
private def remainingCalls (q : State) : ℕ :=
  2 * (q.context.size - q.cursor) - if q.memberPhase then 1 else 0

private theorem advance_progress {q : State} (hlive : halted q = false)
    (reply : Option Bool) (hnext : halted (advance q reply) = false) :
    remainingCalls (advance q reply) < remainingCalls q := by
  have hi : q.cursor < q.context.size := by
    simpa only [decide_eq_false_iff_not, Nat.not_le] using
      (show decide (q.context.size ≤ q.cursor) = false from
        (Bool.or_eq_false_iff.mp hlive).2)
  cases reply with
  | none => simp [advance, halted] at hnext
  | some hit => cases hp : q.memberPhase <;> cases hit <;>
      simp [remainingCalls, advance, observe, predecessorStep, hp, pure, bind,
        Except.pure, Except.bind] <;> omega

/-- The query loop reaches a stopped caller if every requested callee first halts. This
constructs a finite query-machine call trace; it is not a native counting-compiler theorem.
Only valid retained caller states require the generic callee termination contract. -/
theorem exists_stopped_returns {τ : Type} (ctx : Context) (N : QueryMachine τ)
    (start : State → τ) (answer : τ → Option Bool) (w : List Bool)
    (ht : ∀ q : State, q.context = ctx → Bounded q → halted q = false →
      ∃ T, (∀ i < T, N.halted (N.runFrom w (start q) i) = false) ∧
        N.halted (N.runFrom w (start q) T) = true) :
    ∃ q, Returns ctx N start answer w q ∧ halted q = true := by
  have finish (q : State) : Returns ctx N start answer w q →
      ∃ r, Returns ctx N start answer w r ∧ halted r = true := by
    induction q using (measure remainingCalls).wf.induction with
    | h q ih =>
      intro hq
      cases hl : halted q with
      | true => exact ⟨q, hq, hl⟩
      | false =>
        obtain ⟨T, hpre, hhalt⟩ := ht q hq.context_eq hq.bounded hl
        let r := advance q (answer (N.runFrom w (start q) T))
        have hr : Returns ctx N start answer w r := Returns.call hq hl T hpre hhalt
        cases hstop : halted r with
        | true => exact ⟨r, hr, hstop⟩
        | false => exact ih r (advance_progress hl _ hstop) hr
  exact finish (initial ctx) Returns.initial

/-- Conditional agreement with the actual full predecessor fold after a finite return trace.
The callback contract supplies both ordinary Boolean answers and rejection. This does not
construct a trace for arbitrary native callees or supply native first-halting count composition. -/
theorem result_of_returns {τ : Type} {n : ℕ} {ctx : Context} {N : QueryMachine τ}
    {start : State → τ} {answer : τ → Option Bool} {w : List Bool} {q : State}
    (edge : Fin n → Fin n → Option Bool) (member : Fin n → Option Bool) (v : Fin n)
    (hsize : ctx.size = n) (h : Returns ctx N start answer w q) (hstop : halted q = true)
    (hc : ∀ p : State, p.context = ctx → ∀ hi : p.cursor < n, ∀ T,
      (∀ i < T, N.halted (N.runFrom w (start p) i) = false) →
      N.halted (N.runFrom w (start p) T) = true →
      answer (N.runFrom w (start p) T) =
        if p.memberPhase then member ⟨p.cursor, hi⟩ else edge ⟨p.cursor, hi⟩ v) :
    result q = countPredecessors edge member v := by
  change (if q.rejected then none else some q.count) = countPredecessors edge member v
  have hs : remaining edge member v q = countPredecessors edge member v := by
    clear hstop
    induction h with
    | initial => exact remaining_initial edge member v ctx
    | @call p h hlive T hpre hhalt ih =>
      have hp := h.context_eq
      have hr : p.rejected = false := Bool.or_eq_false_iff.mp hlive |>.1
      have hi : p.cursor < n := by
        have hlt := Bool.or_eq_false_iff.mp hlive |>.2
        simp only [decide_eq_false_iff_not, Nat.not_le, hp, hsize] at hlt
        exact hlt
      exact (remaining_advance edge member v p hi hr _ (hc p hp hi T hpre hhalt)).trans ih
  have hp := h.context_eq
  cases hr : q.rejected with
  | true => simpa [remaining, hr] using hs
  | false =>
    have hge : n ≤ q.cursor := by
      simpa [halted, hr, hp, hsize] using hstop
    simpa [remaining, hr, Nat.not_lt.mpr hge, suffix, Nat.sub_eq_zero_of_le hge,
      Fin.foldlM_zero] using hs

/-- Every clock during a call charges the framed suspended caller and the full live callee.
The bound includes the resume state even for rejection. Initializer/answer component costs are
separate requirements in `machine_next_inSpace`, not silently included in this word-size bound. -/
theorem runFrom_call_encoding_le {τ : Type} (encT : τ ↪ List Bool)
    (ctx : Context) (N : QueryMachine τ) (start : State → τ) (answer : τ → Option Bool)
    (w : List Bool) (q : State) (hq : Bounded q) (hlive : halted q = false) (T D : ℕ)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start q) i) = false)
    (hhalt : N.halted (N.runFrom w (start q) T) = true)
    (hcallee : ∀ i ≤ T, (encT (N.runFrom w (start q) i)).length ≤ D)
    (i : ℕ) (hi : i ≤ T + 2) :
    (encMachineState encT ((machine ctx N start answer).runFrom w (.inl q) i)).length ≤
      4 * (encContext q.context).length + 8 * (Nat.log2 q.context.size + 1) + D + 16 := by
  let C := 2 * (encContext q.context).length + 4 * (Nat.log2 q.context.size + 1) + 7
  have hresume := length_encState_le (advance_bounded hq hlive
    (answer (N.runFrom w (start q) T)))
  rw [advance_context] at hresume
  have h := QueryMachine.withCalls_runFrom_call_encoding_le (caller ctx) N
    (request start) (resume answer) w encState encT hlive (by simp [request, hlive])
    hpre hhalt (length_encState_le hq) hresume hcallee i hi
  change (encMachineState encT ((machine ctx N start answer).runFrom w (.inl q) i)).length ≤
    2 * C + D + 2 at h
  dsimp only [C] at h
  omega

end Turing.DoubleCounting.Predecessor
