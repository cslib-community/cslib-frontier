/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Basic
public import CslibFrontier.Computability.Distributed.ConcurrentObjects.Progress
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability.Nonblocking

/-!
# Treiber's Lock-Free `CAS` Stack (Fresh-Node Step)

This module formalizes a fresh-node (ABA-free) step toward **Treiber's lock-free `CAS` stack**
(#7501; after [Treiber1986]; [Hendler, Shavit, and Yerushalmi, §§2.1–2.2, Fig. 2–3, p. 208,
§§2.2–2.3, p. 209, and §5, Definition 5.1, Lemma 5.13, and Theorem 5.17,
pp. 212–215][HendlerShavitYerushalmi2004]; [Moir and Shavit, §1.3,
pp. 1-15–1-16][MoirShavit2007]), where each `push` allocates a fresh node index at `heap.length`
rather than recycling popped nodes through an ABA version-tagged free list.

Both `push` and `pop` are modeled as **fine-grained multi-step state machines** over shared heap
nodes and a shared `CAS` head pointer `head : Option ℕ`:
* `push(v)`: allocate a fresh heap node `node` holding `v` (`pushAlloc`), read `top := head` and
  link `heap[node].next := top` (`pushRead`), then execute `CAS(&head, top, some node)` (`pushCAS`),
  retrying from `pushRead` on `CAS` failure or entering `returning .pushAck` on `CAS` success before
  emitting the response event.
* `pop()`: read `top := head` (`popRead`); if `head = none`, linearize immediately into
  `returning (.popRet none)`; if `head = some top`, read `(val, nxt) := heap[top]` (`popNext`) and
  execute `CAS(&head, some top, nxt)` (`popCAS`), retrying from `popRead` on `CAS` failure or
  entering `returning (.popRet (some val))` on `CAS` success before emitting the response event.

## Main definitions

* `Cslib.Distributed.ConcurrentObjects.StackOp`,
  `Cslib.Distributed.ConcurrentObjects.StackResp`,
  `Cslib.Distributed.ConcurrentObjects.stackStep`,
  `Cslib.Distributed.ConcurrentObjects.stackSeqSpec`: sequential LIFO stack specification over
  `List V` ([Hendler, Shavit, and Yerushalmi, §5, Definition 5.1,
  p. 212][HendlerShavitYerushalmi2004]).
* `Cslib.Distributed.ConcurrentObjects.StackNode`,
  `Cslib.Distributed.ConcurrentObjects.TreiberPhase`,
  `Cslib.Distributed.ConcurrentObjects.TreiberFreshNodeState`: shared heap nodes, fine-grained
  per-thread control phases, and global fresh-node Treiber stack configurations.
* `Cslib.Distributed.ConcurrentObjects.treiberFreshNodeStep`,
  `Cslib.Distributed.ConcurrentObjects.treiberFreshNodeSystem`: multi-step operational semantics and
  `ProgressSystem` instance for Treiber's stack in the fresh-node model.

## Main results

* `Cslib.Distributed.ConcurrentObjects.treiberFreshNode_isLinearizable`: fresh-node step for #7501
  showing every reachable fresh-node Treiber stack configuration has a linearizable concurrent
  history with respect to `stackSeqSpec`, with linearization points at successful `pushCAS`, empty
  `popRead`, and successful `popCAS` (after [Hendler, Shavit, and Yerushalmi, §5, Lemma 5.13,
  p. 214][HendlerShavitYerushalmi2004]).
* `Cslib.Distributed.ConcurrentObjects.treiberFreshNode_isLockFree`: fresh-node step for #7501
  showing `treiberFreshNodeSystem` is lock-free over finitely many processes (`[Finite P]`, after
  [Hendler, Shavit, and Yerushalmi, §5, Theorem 5.17, p. 215][HendlerShavitYerushalmi2004]).
* `Cslib.Distributed.ConcurrentObjects.treiberFreshNode_cas_fail_witnesses_intervening_cas`:
  fresh-node contention-witness step for #7501 showing that whenever a thread reads
  `expected := head` and later fails its `CAS` because `head ≠ expected` without having modified
  `head` itself in between, another thread `q ≠ p` executed an intervening successful `CAS` on
  `head` and entered `.returning`.

## References

* [R. K. Treiber, *Systems Programming: Coping with Parallelism*][Treiber1986]
* [D. Hendler, N. Shavit, L. Yerushalmi,
  *A Scalable Lock-Free Stack Algorithm*][HendlerShavitYerushalmi2004]
* [M. Moir, N. Shavit, *Concurrent Data Structures*][MoirShavit2007]
-/

public section

namespace Cslib.Distributed.ConcurrentObjects

open Cslib

universe u

/-! ### Sequential LIFO stack specification -/

/-- Operations on a concurrent LIFO stack over element type `V`. -/
inductive StackOp (V : Type u) where
  /-- Push `val` onto the top of the stack. -/
  | push (val : V)
  /-- Pop and return the top element, or `none` if the stack is empty. -/
  | pop
  deriving @[expose] DecidableEq

/-- Responses returned by a concurrent LIFO stack over element type `V`. -/
inductive StackResp (V : Type u) where
  /-- Acknowledge completion of `push`. -/
  | pushAck
  /-- Return `some v` for the popped top element, or `none` when the stack was empty. -/
  | popRet (val : Option V)
  deriving @[expose] DecidableEq

/-- Deterministic sequential LIFO transition function on `List V`
([HendlerShavitYerushalmi2004], §5, Definition 5.1, p. 212). -/
@[expose]
def stackStep {V : Type u} (stk : List V) : StackOp V → List V × StackResp V
  | .push v => (v :: stk, .pushAck)
  | .pop =>
    match stk with
    | [] => ([], .popRet none)
    | v :: rest => (rest, .popRet (some v))

/-- Sequential specification of a LIFO stack over `V` initialized to `[]`. -/
def stackSeqSpec {P : Type u} (V : Type u) :
    SeqSpec P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V) () :=
  SeqSpec.ofMachine () ([] : List V) stackStep

/-! ### Fine-grained multi-step Treiber stack machine (fresh-node model) -/

/-- Linked heap node in Treiber's stack holding an element `val` and next-pointer `next`. -/
@[ext]
structure StackNode (V : Type u) where
  /-- Element value stored in this node. -/
  val : V
  /-- Heap index of the next node down the stack, or `none` at the bottom. -/
  next : Option ℕ
  deriving @[expose] DecidableEq

/-- Fine-grained local execution phase of a thread in the fresh-node Treiber stack
([Hendler, Shavit, and Yerushalmi, §2.2, Fig. 3, p. 208][HendlerShavitYerushalmi2004]). -/
inductive TreiberPhase (V : Type u) where
  /-- Idle: no pending operation. -/
  | idle
  /-- Invoked `push val`: ready to allocate a fresh heap node initialized with `val`. -/
  | pushAlloc (val : V)
  /-- Allocated fresh heap node `node` holding `val`: ready to read `top := head` and link
  `heap[node].next := top`. -/
  | pushRead (val : V) (node : ℕ)
  /-- Linked `heap[node] = ⟨val, expected⟩`: ready to execute `CAS(&head, expected, some node)`,
  retrying from `pushRead val node` on failure. -/
  | pushCAS (val : V) (node : ℕ) (expected : Option ℕ)
  /-- Invoked `pop`: ready to read `top := head` (linearizing immediately if `head = none`). -/
  | popRead
  /-- Observed `head = some top`: ready to read `heap[top]`. -/
  | popNext (top : ℕ)
  /-- Read `heap[top] = ⟨retVal, nxt⟩`: ready to execute `CAS(&head, some top, nxt)`, retrying from
  `popRead` on failure. -/
  | popCAS (top : ℕ) (nxt : Option ℕ) (retVal : V)
  /-- Operation has already linearized with `resp`; ready to append `.resp` to `history` and return
  to `idle`. -/
  | returning (resp : StackResp V)
  deriving @[expose] DecidableEq

namespace TreiberPhase

variable {V : Type u}

/-- Whether a phase is a `.returning` phase (the operation has linearized and will finish on its
next step). -/
private def IsReturning : TreiberPhase V → Prop
  | .returning _ => True
  | _ => False

/-- Exclusive ownership of an unlinked newly allocated node index `node`. -/
private def OwnsNode : TreiberPhase V → ℕ → Prop
  | .pushRead _ n, node => n = node
  | .pushCAS _ n _, node => n = node
  | _, _ => False

/-- Bounded solo-progress rank when `head` remains constant across non-completing steps. -/
private def rank (head : Option ℕ) : TreiberPhase V → ℕ
  | .idle => 0
  | .returning _ => 0
  | .pushCAS _ _ exp => if head = exp then 1 else 4
  | .popCAS top _ _ => if head = some top then 1 else 4
  | .popNext top => if head = some top then 2 else 5
  | .pushRead _ _ => 3
  | .popRead => 3
  | .pushAlloc _ => 4

end TreiberPhase

/-- Global configuration of Treiber's lock-free `CAS` stack in the fresh-node model:
`heap` stores allocated `StackNode`s, `head` holds the optional index of the top node, `threads`
tracks each process's fine-grained control phase, and `history` records all external invocation and
response events observed so far. -/
@[ext]
structure TreiberFreshNodeState (P V : Type u) where
  /-- Monotonically growing array of allocated stack nodes. -/
  heap : List (StackNode V)
  /-- Shared `CAS` pointer to the current top node (`none` when empty). -/
  head : Option ℕ
  /-- Per-process fine-grained execution phase. -/
  threads : P → TreiberPhase V
  /-- Recorded external concurrent invocation/response history on the stack (`Obj = Unit`). -/
  history : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)

/-- Initial empty configuration of the fresh-node Treiber stack. -/
@[expose]
def treiberFreshNodeInit (P V : Type u) : TreiberFreshNodeState P V where
  heap := []
  head := none
  threads := fun _ => .idle
  history := []

/-- `treiberFreshNodeInvoke s p s'` holds when idle process `p` invokes either `push v` or `pop`,
appending the corresponding invocation event to `s.history`. -/
@[expose]
def treiberFreshNodeInvoke {P V : Type u} [DecidableEq P]
    (s : TreiberFreshNodeState P V) (p : P) (s' : TreiberFreshNodeState P V) : Prop :=
  s.threads p = .idle ∧
    ((∃ v : V,
        s' = { s with
          threads := Function.update s.threads p (.pushAlloc v)
          history := s.history ++ [.inv p () (.push v)] }) ∨
      s' = { s with
        threads := Function.update s.threads p .popRead
        history := s.history ++ [.inv p () .pop] })

/-- Execute one fine-grained step of active process `p` in the fresh-node Treiber stack, returning
`(nextState, completed)`. -/
@[expose]
def treiberFreshNodeStep {P V : Type u} [DecidableEq P]
    (s : TreiberFreshNodeState P V) (p : P) : TreiberFreshNodeState P V × Bool :=
  match s.threads p with
  | .idle => (s, false)
  | .pushAlloc v =>
    let node := s.heap.length
    ({ s with
        heap := s.heap ++ [⟨v, none⟩]
        threads := Function.update s.threads p (.pushRead v node) }, false)
  | .pushRead v node =>
    let top := s.head
    ({ s with
        heap := s.heap.set node ⟨v, top⟩
        threads := Function.update s.threads p (.pushCAS v node top) }, false)
  | .pushCAS v node expected =>
    if s.head = expected then
      ({ s with
          head := some node
          threads := Function.update s.threads p (.returning .pushAck) }, false)
    else
      ({ s with
          threads := Function.update s.threads p (.pushRead v node) }, false)
  | .popRead =>
    match s.head with
    | none =>
      ({ s with threads := Function.update s.threads p (.returning (.popRet none)) }, false)
    | some top =>
      ({ s with threads := Function.update s.threads p (.popNext top) }, false)
  | .popNext top =>
    match s.heap[top]? with
    | some nd =>
      ({ s with threads := Function.update s.threads p (.popCAS top nd.next nd.val) }, false)
    | none =>
      ({ s with threads := Function.update s.threads p (.returning (.popRet none)) }, false)
  | .popCAS top nxt retVal =>
    if s.head = some top then
      ({ s with
          head := nxt
          threads := Function.update s.threads p (.returning (.popRet (some retVal))) }, false)
    else
      ({ s with threads := Function.update s.threads p .popRead }, false)
  | .returning resp =>
    ({ s with
        threads := Function.update s.threads p .idle
        history := s.history ++ [.resp p () resp] }, true)

private theorem treiberFreshNodeStep_threads_of_ne {P V : Type u} [DecidableEq P]
    (s : TreiberFreshNodeState P V) {p q : P} (hqp : q ≠ p) :
    (treiberFreshNodeStep s p).1.threads q = s.threads q := by
  cases htp : s.threads p with
  | idle => simp only [treiberFreshNodeStep, htp]
  | pushAlloc _ => simp only [treiberFreshNodeStep, htp, Function.update_of_ne hqp]
  | pushRead _ _ => simp only [treiberFreshNodeStep, htp, Function.update_of_ne hqp]
  | pushCAS _ _ exp =>
    by_cases hc : s.head = exp <;>
      simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_of_ne hqp]
  | popRead =>
    cases hh : s.head <;>
      simp only [treiberFreshNodeStep, htp, hh, Function.update_of_ne hqp]
  | popNext top =>
    cases hnd : s.heap[top]? <;>
      simp only [treiberFreshNodeStep, htp, hnd, Function.update_of_ne hqp]
  | popCAS top _ _ =>
    by_cases hc : s.head = some top <;>
      simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_of_ne hqp]
  | returning _ => simp only [treiberFreshNodeStep, htp, Function.update_of_ne hqp]

/-- `ProgressSystem` of Treiber's lock-free `CAS` stack in the fresh-node model. -/
@[expose]
def treiberFreshNodeSystem (P V : Type u) [DecidableEq P] : ProgressSystem P where
  State := TreiberFreshNodeState P V
  init := treiberFreshNodeInit P V
  Active s p := s.threads p ≠ .idle
  Invoke := treiberFreshNodeInvoke
  step := treiberFreshNodeStep
  invoke_only_idle := by
    rintro s p _ ⟨hp, _⟩ hact
    exact hact hp
  active_after_invoke := by
    rintro s p _ ⟨_, ⟨v, rfl⟩ | rfl⟩ <;>
      simp only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true]
  invoke_frame_active := by
    rintro s p q _ ⟨_, ⟨v, rfl⟩ | rfl⟩ hqp <;>
      simp only [ne_eq, Function.update_of_ne hqp]
  active_after_step_false := by
    intro s p hact hfalse
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | pushAlloc v =>
      simp only [treiberFreshNodeStep, htp, ne_eq, Function.update_self, reduceCtorEq,
        not_false_eq_true]
    | pushRead v node =>
      simp only [treiberFreshNodeStep, htp, ne_eq, Function.update_self, reduceCtorEq,
        not_false_eq_true]
    | pushCAS v node exp =>
      by_cases hc : s.head = exp <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, ne_eq, Function.update_self,
          reduceCtorEq, not_false_eq_true]
    | popRead =>
      cases hh : s.head <;>
        simp only [treiberFreshNodeStep, htp, hh, ne_eq, Function.update_self, reduceCtorEq,
          not_false_eq_true]
    | popNext top =>
      cases hnd : s.heap[top]? <;>
        simp only [treiberFreshNodeStep, htp, hnd, ne_eq, Function.update_self, reduceCtorEq,
          not_false_eq_true]
    | popCAS top nxt retVal =>
      by_cases hc : s.head = some top <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, ne_eq, Function.update_self,
          reduceCtorEq, not_false_eq_true]
    | returning resp =>
      simp only [treiberFreshNodeStep, htp, Bool.true_eq_false] at hfalse
  idle_after_step_true := by
    intro s p hact htrue
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | pushAlloc _ => simp only [treiberFreshNodeStep, htp, Bool.false_eq_true] at htrue
    | pushRead _ _ => simp only [treiberFreshNodeStep, htp, Bool.false_eq_true] at htrue
    | pushCAS _ _ exp =>
      by_cases hc : s.head = exp <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Bool.false_eq_true] at htrue
    | popRead =>
      cases hh : s.head <;>
        simp only [treiberFreshNodeStep, htp, hh, Bool.false_eq_true] at htrue
    | popNext top =>
      cases hnd : s.heap[top]? <;>
        simp only [treiberFreshNodeStep, htp, hnd, Bool.false_eq_true] at htrue
    | popCAS top _ _ =>
      by_cases hc : s.head = some top <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Bool.false_eq_true] at htrue
    | returning resp =>
      simp only [treiberFreshNodeStep, htp, ne_eq, Function.update_self, not_true_eq_false,
        not_false_eq_true]
  step_frame_active := by
    intro s p q _ hqp
    simp only [ne_eq, treiberFreshNodeStep_threads_of_ne s hqp]

/-! ### Lock-freedom and contention witness (`CAS` failure implies intervening `CAS`) -/

private theorem treiberFreshNodeStep_head_ne {P V : Type u} [DecidableEq P]
    {s : TreiberFreshNodeState P V} {p : P}
    (hne : (treiberFreshNodeStep s p).1.head ≠ s.head) :
    (treiberFreshNodeStep s p).2 = false ∧
      ∃ resp : StackResp V, (treiberFreshNodeStep s p).1.threads p = .returning resp := by
  cases htp : s.threads p with
  | idle => simp only [treiberFreshNodeStep, htp, ne_eq, not_true_eq_false] at hne
  | pushAlloc _ => simp only [treiberFreshNodeStep, htp, ne_eq, not_true_eq_false] at hne
  | pushRead _ _ => simp only [treiberFreshNodeStep, htp, ne_eq, not_true_eq_false] at hne
  | pushCAS v node exp =>
    by_cases hc : s.head = exp
    · simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_self]
      exact ⟨trivial, .pushAck, rfl⟩
    · simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, ne_eq, not_true_eq_false] at hne
  | popRead =>
    cases hh : s.head <;>
      simp only [treiberFreshNodeStep, htp, hh, ne_eq, not_true_eq_false] at hne
  | popNext top =>
    cases hnd : s.heap[top]? <;>
      simp only [treiberFreshNodeStep, htp, hnd, ne_eq, not_true_eq_false] at hne
  | popCAS top nxt retVal =>
    by_cases hc : s.head = some top
    · simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_self]
      exact ⟨trivial, .popRet (some retVal), rfl⟩
    · simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, ne_eq, not_true_eq_false] at hne
  | returning _ => simp only [treiberFreshNodeStep, htp, ne_eq, not_true_eq_false] at hne

/-- Fresh-node model step for #7501, not the cited endpoint (after [Treiber1986];
[Hendler, Shavit, and Yerushalmi, §5, Theorem 5.17, p. 215][HendlerShavitYerushalmi2004]):
`treiberFreshNodeSystem` is lock-free over finitely many processes (`[Finite P]`), instantiated via
`ProgressSystem.isLockFree_of_bounded_shared_changes`, leaving the ABA version-tagged free-list
recycling model open in #7501. -/
theorem treiberFreshNode_isLockFree (P V : Type u) [DecidableEq P] [Finite P] :
    (treiberFreshNodeSystem P V).IsLockFree := by
  refine ProgressSystem.isLockFree_of_bounded_shared_changes
    (sys := treiberFreshNodeSystem P V)
    (shared := TreiberFreshNodeState.head)
    (Committed := fun s p => (s.threads p).IsReturning)
    (rank := fun s p => TreiberPhase.rank s.head (s.threads p))
    ?_ ?_ ?_ ?_ ?_
  · intro s p _ _ hsh_ne
    obtain ⟨_, resp, hret⟩ := treiberFreshNodeStep_head_ne hsh_ne
    dsimp only [treiberFreshNodeSystem]
    rw [hret]
    trivial
  · intro s p q _ _ hqp hcomm
    dsimp only [treiberFreshNodeSystem]
    rwa [treiberFreshNodeStep_threads_of_ne s hqp]
  · intro s p _ hcomm
    cases htp : s.threads p with
    | returning _ => simp only [treiberFreshNodeSystem, treiberFreshNodeStep, htp]
    | idle | pushAlloc _ | pushRead _ _ | pushCAS _ _ _ | popRead | popNext _ | popCAS _ _ _ =>
      rw [htp] at hcomm; exact False.elim hcomm
  · intro s p hact hfalse _
    dsimp only [treiberFreshNodeSystem] at hact hfalse ⊢
    cases htp : s.threads p with
    | idle => exact absurd htp hact
    | pushAlloc v =>
      simp only [treiberFreshNodeStep, htp, Function.update_self, TreiberPhase.rank]
      omega
    | pushRead v node =>
      simp only [treiberFreshNodeStep, htp, Function.update_self, TreiberPhase.rank, ↓reduceIte]
      omega
    | pushCAS v node exp =>
      by_cases hc : s.head = exp <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_self,
          TreiberPhase.rank] <;>
        omega
    | popRead =>
      cases hh : s.head <;>
        simp only [treiberFreshNodeStep, htp, hh, Function.update_self, TreiberPhase.rank,
          ↓reduceIte] <;>
        omega
    | popNext top =>
      cases hnd : s.heap[top]? with
      | some nd =>
        by_cases hc : s.head = some top <;>
          simp only [treiberFreshNodeStep, htp, hnd, Function.update_self, TreiberPhase.rank, hc,
            ↓reduceIte] <;>
          omega
      | none =>
        by_cases hc : s.head = some top <;>
          simp only [treiberFreshNodeStep, htp, hnd, Function.update_self, TreiberPhase.rank, hc,
            ↓reduceIte] <;>
          omega
    | popCAS top nxt retVal =>
      by_cases hc : s.head = some top <;>
        simp only [treiberFreshNodeStep, htp, hc, ↓reduceIte, Function.update_self,
          TreiberPhase.rank] <;>
        omega
    | returning resp =>
      simp only [treiberFreshNodeStep, htp, Bool.true_eq_false] at hfalse
  · intro s p q _ _ hsh_eq hqp
    dsimp only [treiberFreshNodeSystem] at hsh_eq ⊢
    rw [hsh_eq, treiberFreshNodeStep_threads_of_ne s hqp]

/-- Fresh-node contention-witness step for #7501, not the cited endpoint (after
[Hendler, Shavit, and Yerushalmi, §5, Theorem 5.17, p. 215][HendlerShavitYerushalmi2004]): along
any finite execution segment `states 0 → ... → states k` of `treiberFreshNodeSystem`, if thread `p`
observed `(states 0).head = expected`, later encounters `(states k).head ≠ expected` (causing `p`'s
`CAS` to fail and retry), and did not itself modify `head` during `[0, k)`, then another thread
`q ≠ p` executed a successful `CAS` at an intervening step `j < k`, modifying `head` and entering
`.returning resp`. -/
theorem treiberFreshNode_cas_fail_witnesses_intervening_cas {P V : Type u} [DecidableEq P]
    {states : ℕ → TreiberFreshNodeState P V} {labels : ℕ → StepLabel P} {k : ℕ}
    {p : P} {expected : Option ℕ}
    (htr : ∀ i < k, (treiberFreshNodeSystem P V).lts.Tr (states i) (labels i) (states (i + 1)))
    (hread : (states 0).head = expected)
    (hfail : (states k).head ≠ expected)
    (hp_no_mod : ∀ i < k, (labels i).proc = p → (states (i + 1)).head = (states i).head) :
    ∃ (j : ℕ) (q : P) (resp : StackResp V),
      j < k ∧ q ≠ p ∧ labels j = .exec q false ∧
        (states (j + 1)).head ≠ (states j).head ∧
        (states (j + 1)).threads q = .returning resp := by
  have hex_chg : ∃ j < k, (states (j + 1)).head ≠ (states j).head := by
    by_contra hconst
    have heq_all : ∀ m ≤ k, (states m).head = expected := by
      intro m hm
      induction m with
      | zero => exact hread
      | succ m' ih =>
        have hm' : (states m').head = expected := ih (by omega)
        have hstep_eq : (states (m' + 1)).head = (states m').head := by
          by_contra hne
          exact hconst ⟨m', by omega, hne⟩
        exact hstep_eq.trans hm'
    exact hfail (heq_all k (Nat.le_refl k))
  obtain ⟨j, hj_lt, hj_chg⟩ := hex_chg
  have htr_j := htr j hj_lt
  cases hlbl : labels j with
  | invoke q =>
    rw [hlbl] at htr_j
    rcases htr_j.2 with ⟨v, hst⟩ | hst <;> (rw [hst] at hj_chg; exact absurd rfl hj_chg)
  | exec q done =>
    rw [hlbl] at htr_j
    obtain ⟨_, hstep_j⟩ := htr_j
    have hs1 : (treiberFreshNodeStep (states j) q).1 = states (j + 1) :=
      congrArg Prod.fst hstep_j
    have hs2 : (treiberFreshNodeStep (states j) q).2 = done :=
      congrArg Prod.snd hstep_j
    have hchg' : (treiberFreshNodeStep (states j) q).1.head ≠ (states j).head := by
      rw [hs1]; exact hj_chg
    obtain ⟨hdone_f, resp, hret⟩ := treiberFreshNodeStep_head_ne hchg'
    rw [hs2] at hdone_f
    subst hdone_f
    rw [hs1] at hret
    have hqp : q ≠ p := fun h => by
      subst h
      exact hj_chg (hp_no_mod j hj_lt (by rw [hlbl]; rfl))
    exact ⟨j, q, resp, hj_lt, hqp, hlbl, hj_chg, hret⟩

/-! ### Spine representation and forward inductive invariant for linearizability -/

section LinearizabilityProof

/-- `ValidSpine heap ptr spine` holds when traversing `next` pointers starting from `ptr` through
`heap` visits the exact in-bounds node indices `spine : List ℕ` and ends at `none`. -/
private def ValidSpine {V : Type u} (heap : List (StackNode V)) : Option ℕ → List ℕ → Prop
  | none, [] => True
  | some idx, headIdx :: rest =>
    idx = headIdx ∧ idx < heap.length ∧
      ∃ nd : StackNode V, heap[idx]? = some nd ∧ ValidSpine heap nd.next rest
  | _, _ => False

/-- Abstract LIFO stack `List V` read along `spine` in `heap`. -/
private def spineVals {V : Type u} (heap : List (StackNode V)) (spine : List ℕ) : List V :=
  spine.filterMap fun idx => (heap[idx]?).map StackNode.val

private theorem ValidSpine.mem_lt {V : Type u} {heap : List (StackNode V)} {ptr : Option ℕ}
    {spine : List ℕ} (h : ValidSpine heap ptr spine) :
    ∀ i ∈ spine, i < heap.length := by
  induction spine generalizing ptr with
  | nil => intro _ hm; exact False.elim (List.not_mem_nil hm)
  | cons hd rest ih =>
    cases ptr with
    | none => exact False.elim h
    | some idx =>
      obtain ⟨rfl, hlt, nd, _, hrest⟩ := h
      intro i hm
      rcases List.mem_cons.mp hm with rfl | hmr
      · exact hlt
      · exact ih hrest i hmr

private theorem ValidSpine.congr_heap {V : Type u} {heap₁ heap₂ : List (StackNode V)}
    {ptr : Option ℕ} {spine : List ℕ} (h : ValidSpine heap₁ ptr spine)
    (heq : ∀ i ∈ spine, heap₂[i]? = heap₁[i]? ∧ i < heap₂.length) :
    ValidSpine heap₂ ptr spine ∧ spineVals heap₂ spine = spineVals heap₁ spine := by
  induction spine generalizing ptr with
  | nil =>
    cases ptr with
    | none => exact ⟨trivial, rfl⟩
    | some _ => exact False.elim h
  | cons hd rest ih =>
    cases ptr with
    | none => exact False.elim h
    | some idx =>
      obtain ⟨rfl, _, nd, hnd₁, hrest⟩ := h
      obtain ⟨hnd₂_eq, hlt₂⟩ := heq idx List.mem_cons_self
      have hnd₂ : heap₂[idx]? = some nd := hnd₂_eq.trans hnd₁
      obtain ⟨hsp₂, hvals₂⟩ :=
        ih hrest (fun i hi => heq i (List.mem_cons_of_mem _ hi))
      refine ⟨⟨rfl, hlt₂, nd, hnd₂, hsp₂⟩, ?_⟩
      dsimp only [spineVals, List.filterMap_cons]
      rw [hnd₁, hnd₂]
      exact congrArg (nd.val :: ·) hvals₂

/-- `EvalStack stk cs stkOut` holds when executing the completed stack calls `cs` sequentially from
`stk` produces responses matching `cs` and ends in abstract stack `stkOut`. -/
private def EvalStack {P V : Type u} :
    List V → List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)) →
      List V → Prop
  | stk, [], stkOut => stk = stkOut
  | stk, c :: rest, stkOut =>
    c.res = (stackStep stk c.op).2 ∧ EvalStack (stackStep stk c.op).1 rest stkOut

private theorem evalStack_snoc {P V : Type u} {stk stk₁ stk₂ : List V}
    {cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))}
    (p : P) (op : StackOp V) (resp : StackResp V)
    (heval : EvalStack stk cs stk₁) (hstep : stackStep stk₁ op = (stk₂, resp)) :
    EvalStack stk (cs ++ [⟨p, (), op, resp⟩]) stk₂ := by
  induction cs generalizing stk with
  | nil =>
    subst heval
    exact ⟨by rw [hstep], by rw [hstep]; rfl⟩
  | cons c rest ih =>
    exact ⟨heval.1, ih heval.2⟩

private theorem evalStack_mem_allowed {P V : Type u} {stk stk₁ : List V}
    {cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))}
    (heval : EvalStack stk cs stk₁) :
    SeqSpec.evalMachine () stackStep stk (cs.flatMap OpCall.toEvents) := by
  induction cs generalizing stk with
  | nil => trivial
  | cons c rest ih =>
    cases c with
    | mk p u op res =>
      cases u
      exact ⟨rfl, rfl, rfl, heval.1.symm, ih heval.2⟩

private def ProcHistoryMatch {P V : Type u} [DecidableEq P]
    (H R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))
    (p : P) : TreiberPhase V → Prop
  | .idle =>
    History.procSubhistory R p = [] ∧
      ∃ cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)),
        History.procSubhistory H p = cs.flatMap OpCall.toEvents
  | .pushAlloc v | .pushRead v _ | .pushCAS v _ _ =>
    History.procSubhistory R p = [] ∧
      ∃ cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)),
        History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p () (.push v)]
  | .popRead | .popNext _ | .popCAS _ _ _ =>
    History.procSubhistory R p = [] ∧
      ∃ cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)),
        History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p () .pop]
  | .returning resp =>
    History.procSubhistory R p = [.resp p () resp] ∧
      ∃ (cs : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)))
        (op : StackOp V),
        History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p () op]

private theorem procHistoryMatch_congr {P V : Type u} [DecidableEq P]
    {H₁ H₂ R₁ R₂ : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)}
    {q : P} {ph : TreiberPhase V}
    (hH : History.procSubhistory H₁ q = History.procSubhistory H₂ q)
    (hR : History.procSubhistory R₁ q = History.procSubhistory R₂ q)
    (h : ProcHistoryMatch H₂ R₂ q ph) :
    ProcHistoryMatch H₁ R₁ q ph := by
  cases ph <;> simpa only [ProcHistoryMatch, hH, hR] using h

private theorem wellFormed_of_procHistoryMatch {P V : Type u} [DecidableEq P]
    {H R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)}
    {threads : P → TreiberPhase V}
    (hm : ∀ p, ProcHistoryMatch H R p (threads p)) :
    History.WellFormed (H ++ R) := by
  have hseq_inv : ∀ (cs : List (OpCall P (fun _ : Unit => StackOp V)
      (fun _ : Unit => StackResp V))) (p : P) (op : StackOp V),
      History.IsSequential (cs.flatMap OpCall.toEvents ++ [.inv p () op]) := by
    intro cs p op
    induction cs with
    | nil => trivial
    | cons c rest ih => exact ⟨rfl, rfl, ih⟩
  intro p
  rw [History.procSubhistory_append]
  have hp := hm p
  generalize threads p = ph at hp
  cases ph with
  | idle =>
    obtain ⟨hR, cs, hH⟩ := hp
    rw [hR, List.append_nil, hH]
    exact History.isSequential_flatMap_toEvents cs
  | pushAlloc _ | pushRead _ _ | pushCAS _ _ _ | popRead | popNext _ | popCAS _ _ _ =>
    obtain ⟨hR, cs, hH⟩ := hp
    rw [hR, List.append_nil, hH]
    exact hseq_inv cs p _
  | returning resp =>
    obtain ⟨hR, cs, op, hH⟩ := hp
    rw [hR, hH]
    have hpair := History.isSequential_append_pair
      (History.isSequential_flatMap_toEvents cs)
      (by rw [History.length_flatMap_toEvents]; omega) p () op resp
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hpair

/-- Heap and fresh-node ownership invariant relating `heap`, `spine`, and `threads`. -/
private structure NodeOwnershipInv {P V : Type u}
    (heap : List (StackNode V)) (spine : List ℕ) (threads : P → TreiberPhase V) : Prop where
  own_lt : ∀ p node, (threads p).OwnsNode node → node < heap.length
  own_not_spine : ∀ p node, (threads p).OwnsNode node → node ∉ spine
  own_uniq : ∀ p q node, (threads p).OwnsNode node → (threads q).OwnsNode node → p = q
  pushCAS_nd : ∀ p v node exp, threads p = .pushCAS v node exp → heap[node]? = some ⟨v, exp⟩
  popNext_ok : ∀ p top, threads p = .popNext top →
    top < heap.length ∧ ∀ q, ¬ (threads q).OwnsNode top
  popCAS_ok : ∀ p top nxt val, threads p = .popCAS top nxt val →
    top < heap.length ∧ (∀ q, ¬ (threads q).OwnsNode top) ∧ heap[top]? = some ⟨val, nxt⟩

/-- Updating `threads p` to any phase `ph` that introduces no new node ownership and is not a
`pushCAS`, `popNext`, or `popCAS` phase preserves `NodeOwnershipInv` (for any `spine'` disjoint from
remaining owned nodes). -/
private theorem NodeOwnershipInv.update_nonSpecial {P V : Type u} [DecidableEq P]
    {heap : List (StackNode V)} {spine spine' : List ℕ} {threads : P → TreiberPhase V}
    {p : P} {ph : TreiberPhase V} (hn : NodeOwnershipInv heap spine threads)
    (hown_sub : ∀ q n, (Function.update threads p ph q).OwnsNode n → (threads q).OwnsNode n)
    (hsp_disj : ∀ q n, (Function.update threads p ph q).OwnsNode n → n ∉ spine')
    (hnot_pushC : ∀ w n e, ph ≠ .pushCAS w n e)
    (hnot_popN : ∀ t, ph ≠ .popNext t)
    (hnot_popC : ∀ t nx vl, ph ≠ .popCAS t nx vl) :
    NodeOwnershipInv heap spine' (Function.update threads p ph) where
  own_lt q n hq := hn.own_lt q n (hown_sub q n hq)
  own_not_spine := hsp_disj
  own_uniq q₁ q₂ n h₁ h₂ := hn.own_uniq q₁ q₂ n (hown_sub q₁ n h₁) (hown_sub q₂ n h₂)
  pushCAS_nd q w n exp hq := by
    have hqp : q ≠ p := fun h => by
      subst h; rw [Function.update_self] at hq; exact hnot_pushC _ _ _ hq
    rw [Function.update_of_ne hqp] at hq
    exact hn.pushCAS_nd q w n exp hq
  popNext_ok q top hq := by
    have hqp : q ≠ p := fun h => by subst h; rw [Function.update_self] at hq; exact hnot_popN _ hq
    rw [Function.update_of_ne hqp] at hq
    obtain ⟨hlt, hno⟩ := hn.popNext_ok q top hq
    exact ⟨hlt, fun r hr => hno r (hown_sub r top hr)⟩
  popCAS_ok q top nxt val hq := by
    have hqp : q ≠ p := fun h => by
      subst h; rw [Function.update_self] at hq; exact hnot_popC _ _ _ hq
    rw [Function.update_of_ne hqp] at hq
    obtain ⟨hlt, hno, hnd⟩ := hn.popCAS_ok q top nxt val hq
    exact ⟨hlt, fun r hr => hno r (hown_sub r top hr), hnd⟩

/-- Forward inductive invariant of `TreiberFreshNodeState` maintaining the heap spine, fresh-node
ownership disjointness, pending response extension `R` for `.returning` threads, and linearized
call sequence `S_calls`. -/
private def TreiberInv {P V : Type u} [DecidableEq P] (s : TreiberFreshNodeState P V) : Prop :=
  ∃ (spine : List ℕ)
    (R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))
    (S_calls : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))),
    ValidSpine s.heap s.head spine ∧
    NodeOwnershipInv s.heap spine s.threads ∧
    EvalStack ([] : List V) S_calls (spineVals s.heap spine) ∧
    History.IsRespList R ∧
    (∀ p, ProcHistoryMatch s.history R p (s.threads p)) ∧
    History.Equivalent (History.complete (s.history ++ R)) (S_calls.flatMap OpCall.toEvents) ∧
    (∀ e₀ e₁, History.IsCompletedOp (s.history ++ R) e₀ →
      History.IsCompletedOp (s.history ++ R) e₁ →
      History.prec s.history e₀ e₁ → History.prec (S_calls.flatMap OpCall.toEvents) e₀ e₁)

private theorem treiberInv_init (P V : Type u) [DecidableEq P] :
    TreiberInv (treiberFreshNodeInit P V) := by
  refine ⟨[], [], [], trivial, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact
      { own_lt := fun _ _ h => False.elim h
        own_not_spine := fun _ _ h => False.elim h
        own_uniq := fun _ _ _ h _ => False.elim h
        pushCAS_nd := fun _ _ _ _ h => nomatch h
        popNext_ok := fun _ _ h => nomatch h
        popCAS_ok := fun _ _ _ _ h => nomatch h }
  · intro _ hm; exact False.elim (List.not_mem_nil hm)
  · intro p; exact ⟨rfl, [], rfl⟩
  · intro p; rfl
  · intro _ _ hc₀ _ _
    simp only [treiberFreshNodeInit, List.nil_append, History.isCompletedOp_iff_lt_length,
      History.procSubhistory_nil, List.length_nil] at hc₀
    omega

private theorem treiberInv_invoke_op {P V : Type u} [DecidableEq P]
    {s : TreiberFreshNodeState P V} {p : P} (op : StackOp V) (ph : TreiberPhase V)
    (hinv : TreiberInv s) (hp_idle : s.threads p = .idle)
    (hph_no_own : ∀ n, ¬ ph.OwnsNode n)
    (hph_not_pc : ∀ w n e, ph ≠ .pushCAS w n e)
    (hph_not_pn : ∀ t, ph ≠ .popNext t)
    (hph_not_popc : ∀ t nx vl, ph ≠ .popCAS t nx vl)
    (hpm_ph : ∀ {H R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)}
      {cs_p : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))},
      History.procSubhistory R p = [] →
      History.procSubhistory H p = cs_p.flatMap OpCall.toEvents →
      ProcHistoryMatch (H ++ [.inv p () op]) R p ph) :
    TreiberInv
      { s with
        threads := Function.update s.threads p ph
        history := s.history ++ [.inv p () op] } := by
  obtain ⟨spine, R, S_calls, hsp, hnode, heval, hR_resp, hpm, heqS, hprecS⟩ := hinv
  have hwf' := wellFormed_of_procHistoryMatch hpm
  have hpm_p := hpm p
  rw [hp_idle] at hpm_p
  obtain ⟨hRp_nil, cs_p, hHp⟩ := hpm_p
  obtain ⟨_, heq_new, hprec_new⟩ :=
    History.append_pending_inv_extension (Op := fun _ : Unit => StackOp V)
      (Resp := fun _ : Unit => StackResp V) (x := ()) op hwf' heqS hprecS hHp hRp_nil
  have hown_sub :
      ∀ q n, (Function.update s.threads p ph q).OwnsNode n → (s.threads q).OwnsNode n := by
    intro q n hq
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact False.elim (hph_no_own n hq)
    · rwa [Function.update_of_ne hqp] at hq
  refine ⟨spine, R, S_calls, hsp,
    hnode.update_nonSpecial hown_sub (fun q n hq => hnode.own_not_spine q n (hown_sub q n hq))
      hph_not_pc hph_not_pn hph_not_popc,
    heval, hR_resp, ?_, heq_new, hprec_new⟩
  intro q
  dsimp only
  by_cases hqp : q = p
  · subst hqp
    rw [Function.update_self]
    exact hpm_ph hRp_nil hHp
  · rw [Function.update_of_ne hqp]
    have hHq : History.procSubhistory (s.history ++ [.inv p () op]) q =
        History.procSubhistory s.history q := by
      simp only [History.procSubhistory_append, History.procSubhistory_cons, Event.proc_inv,
        Ne.symm hqp, ↓reduceIte, History.procSubhistory_nil, List.append_nil]
    exact procHistoryMatch_congr hHq rfl (hpm q)

private theorem treiberInv_invoke {P V : Type u} [DecidableEq P]
    {s s' : TreiberFreshNodeState P V} {p : P}
    (hinv : TreiberInv s) (htr : treiberFreshNodeInvoke s p s') :
    TreiberInv s' := by
  obtain ⟨hp_idle, ⟨v, rfl⟩ | rfl⟩ := htr
  · exact treiberInv_invoke_op (.push v) (.pushAlloc v) hinv hp_idle
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) fun {_ _ cs_p} hR hH => ⟨hR, cs_p, by
        simp only [History.procSubhistory_append, hH, History.procSubhistory_cons, Event.proc_inv,
          ↓reduceIte, History.procSubhistory_nil]⟩
  · exact treiberInv_invoke_op .pop .popRead hinv hp_idle
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) fun {_ _ cs_p} hR hH => ⟨hR, cs_p, by
        simp only [History.procSubhistory_append, hH, History.procSubhistory_cons, Event.proc_inv,
          ↓reduceIte, History.procSubhistory_nil]⟩

/-- Shared helper updating `(R, S_calls)` when an active unlinearized operation `op` of process `p`
linearizes with response `resp` and new abstract stack `stk'` (without modifying `s.history`). -/
private theorem linearize_step_witness {P V : Type u} [DecidableEq P]
    {H R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)}
    {S_calls : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))}
    {threads threads' : P → TreiberPhase V}
    {stk stk' : List V} {p : P} {op : StackOp V} {resp : StackResp V}
    {cs_p : List (OpCall P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V))}
    (heval : EvalStack ([] : List V) S_calls stk)
    (hstep_stk : stackStep stk op = (stk', resp))
    (hR_resp : History.IsRespList R)
    (hpm : ∀ q, ProcHistoryMatch H R q (threads q))
    (heqS : History.Equivalent (History.complete (H ++ R)) (S_calls.flatMap OpCall.toEvents))
    (hprecS : ∀ e₀ e₁, History.IsCompletedOp (H ++ R) e₀ →
      History.IsCompletedOp (H ++ R) e₁ →
      History.prec H e₀ e₁ → History.prec (S_calls.flatMap OpCall.toEvents) e₀ e₁)
    (hHp : History.procSubhistory H p = cs_p.flatMap OpCall.toEvents ++ [.inv p () op])
    (hRp_nil : History.procSubhistory R p = [])
    (hthr_p : threads' p = .returning resp)
    (hthr_ne : ∀ q ≠ p, threads' q = threads q) :
    let R₁ := R ++ [.resp p () resp]
    let S_calls' := S_calls ++ [⟨p, (), op, resp⟩]
    EvalStack ([] : List V) S_calls' stk' ∧
      History.IsRespList R₁ ∧
      (∀ q, ProcHistoryMatch H R₁ q (threads' q)) ∧
      History.Equivalent (History.complete (H ++ R₁)) (S_calls'.flatMap OpCall.toEvents) ∧
      (∀ e₀ e₁, History.IsCompletedOp (H ++ R₁) e₀ →
        History.IsCompletedOp (H ++ R₁) e₁ →
        History.prec H e₀ e₁ → History.prec (S_calls'.flatMap OpCall.toEvents) e₀ e₁) := by
  intro R₁ S_calls'
  have hwf' := wellFormed_of_procHistoryMatch hpm
  have hseqS := History.isSequential_flatMap_toEvents S_calls
  obtain ⟨hR₁_resp, _, _, heqS', hprecS'⟩ :=
    History.linearize_pending_in_extension (Op := fun _ : Unit => StackOp V)
      (Resp := fun _ : Unit => StackResp V) (x := ()) resp hR_resp hwf' hseqS heqS hprecS hHp
      hRp_nil
  have hS'_eq : S_calls'.flatMap OpCall.toEvents =
      S_calls.flatMap OpCall.toEvents ++ [.inv p () op, .resp p () resp] := by
    simp only [S_calls', List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, OpCall.toEvents]
  rw [← hS'_eq] at heqS' hprecS'
  refine ⟨evalStack_snoc p op resp heval hstep_stk, hR₁_resp, ?_, heqS', hprecS'⟩
  intro q
  by_cases hqp : q = p
  · subst hqp
    rw [hthr_p]
    refine ⟨?_, cs_p, op, hHp⟩
    simp only [R₁, History.procSubhistory_append, hRp_nil, List.nil_append,
      History.procSubhistory_cons, Event.proc_resp, ↓reduceIte, History.procSubhistory_nil]
  · rw [hthr_ne q hqp]
    have hR₁_q : History.procSubhistory R₁ q = History.procSubhistory R q := by
      simp only [R₁, History.procSubhistory_append, History.procSubhistory_cons, Event.proc_resp,
        Ne.symm hqp, ↓reduceIte, History.procSubhistory_nil, List.append_nil]
    exact procHistoryMatch_congr rfl hR₁_q (hpm q)

private theorem procHistoryMatch_update_same {P V : Type u} [DecidableEq P]
    {H R : History P (fun _ : Unit => StackOp V) (fun _ : Unit => StackResp V)}
    {threads : P → TreiberPhase V} {p : P} {ph : TreiberPhase V}
    (hpm : ∀ q, ProcHistoryMatch H R q (threads q))
    (hp : ProcHistoryMatch H R p ph) :
    ∀ q, ProcHistoryMatch H R q (Function.update threads p ph q) := by
  intro q
  by_cases hqp : q = p
  · subst hqp; rw [Function.update_self]; exact hp
  · rw [Function.update_of_ne hqp]; exact hpm q

private theorem treiberInv_exec {P V : Type u} [DecidableEq P]
    {s : TreiberFreshNodeState P V} {p : P}
    (hinv : TreiberInv s) (hact : s.threads p ≠ .idle) :
    TreiberInv (treiberFreshNodeStep s p).1 := by
  obtain ⟨spine, R, S_calls, hsp, hnode, heval, hR_resp, hpm, heqS, hprecS⟩ := hinv
  cases htp : s.threads p with
  | idle => exact absurd htp hact
  | pushAlloc v =>
    -- Heap grows by `[⟨v, none⟩]` at fresh index `node = s.heap.length`.
    rw [treiberFreshNodeStep, htp]
    dsimp only
    have hsp_mem_lt := hsp.mem_lt
    obtain ⟨hsp', hvals'⟩ := hsp.congr_heap (heap₂ := s.heap ++ [⟨v, none⟩]) fun i hi => by
      have hilt := hsp_mem_lt i hi
      exact ⟨List.getElem?_append_left hilt,
        by rw [List.length_append, List.length_cons, List.length_nil]; omega⟩
    have hp_pm : ProcHistoryMatch s.history R p (.pushRead v s.heap.length) := by
      have h := hpm p; rw [htp] at h; exact h
    refine ⟨spine, R, S_calls, hsp', ?_, by rw [hvals']; exact heval, hR_resp,
      procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
    dsimp only
    refine
      { own_lt := ?_
        own_not_spine := ?_
        own_uniq := ?_
        pushCAS_nd := ?_
        popNext_ok := ?_
        popCAS_ok := ?_ }
    · intro q n hq
      rw [List.length_append, List.length_cons, List.length_nil]
      by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq; omega
      · simp only [Function.update_of_ne hqp] at hq; have := hnode.own_lt q n hq; omega
    · intro q n hq
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
        subst hq
        intro hmem; have := hsp_mem_lt _ hmem; omega
      · simp only [Function.update_of_ne hqp] at hq
        exact hnode.own_not_spine q n hq
    · intro q₁ q₂ n h₁ h₂
      by_cases hq₁ : q₁ = p
      · subst hq₁
        simp only [Function.update_self, TreiberPhase.OwnsNode] at h₁
        subst h₁
        by_cases hq₂ : q₂ = q₁
        · exact hq₂.symm
        · simp only [Function.update_of_ne hq₂] at h₂
          have := hnode.own_lt q₂ _ h₂; omega
      · simp only [Function.update_of_ne hq₁] at h₁
        by_cases hq₂ : q₂ = p
        · subst hq₂
          simp only [Function.update_self, TreiberPhase.OwnsNode] at h₂
          subst h₂; have := hnode.own_lt q₁ _ h₁; omega
        · simp only [Function.update_of_ne hq₂] at h₂
          exact hnode.own_uniq q₁ q₂ n h₁ h₂
    · intro q w n exp hq
      have hqp : q ≠ p := fun h => by subst h; simp only [Function.update_self, reduceCtorEq] at hq
      simp only [Function.update_of_ne hqp] at hq
      rw [List.getElem?_append_left (hnode.own_lt q n (by rw [hq]; rfl))]
      exact hnode.pushCAS_nd q w n exp hq
    · intro q top hq
      have hqp : q ≠ p := fun h => by subst h; simp only [Function.update_self, reduceCtorEq] at hq
      simp only [Function.update_of_ne hqp] at hq
      obtain ⟨hlt, hno⟩ := hnode.popNext_ok q top hq
      refine ⟨by rw [List.length_append, List.length_cons, List.length_nil]; omega, fun r hr => ?_⟩
      by_cases hrp : r = p
      · subst hrp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hr; omega
      · simp only [Function.update_of_ne hrp] at hr; exact hno r hr
    · intro q top nxt val hq
      have hqp : q ≠ p := fun h => by subst h; simp only [Function.update_self, reduceCtorEq] at hq
      simp only [Function.update_of_ne hqp] at hq
      obtain ⟨hlt, hno, hnd⟩ := hnode.popCAS_ok q top nxt val hq
      refine ⟨by rw [List.length_append, List.length_cons, List.length_nil]; omega,
        fun r hr => ?_, ?_⟩
      · by_cases hrp : r = p
        · subst hrp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hr; omega
        · simp only [Function.update_of_ne hrp] at hr; exact hno r hr
      · rw [List.getElem?_append_left hlt]; exact hnd
  | pushRead v node =>
    -- `p` exclusively owns `node < s.heap.length`, `node ∉ spine`, and links `heap[node]`.
    rw [treiberFreshNodeStep, htp]
    dsimp only
    have hp_own : (s.threads p).OwnsNode node := by rw [htp]; rfl
    have hnode_lt : node < s.heap.length := hnode.own_lt p node hp_own
    have hnode_nsp : node ∉ spine := hnode.own_not_spine p node hp_own
    have hsp_mem_lt := hsp.mem_lt
    obtain ⟨hsp', hvals'⟩ := hsp.congr_heap (heap₂ := s.heap.set node ⟨v, s.head⟩) fun i hi => by
      have hine : node ≠ i := fun h => hnode_nsp (h ▸ hi)
      exact ⟨List.getElem?_set_ne hine, by rw [List.length_set]; exact hsp_mem_lt i hi⟩
    have hown_iff : ∀ q n,
        (Function.update s.threads p (.pushCAS v node s.head) q).OwnsNode n ↔
          (s.threads q).OwnsNode n := by
      intro q n
      by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, htp, TreiberPhase.OwnsNode]
      · simp only [Function.update_of_ne hqp]
    have hp_pm : ProcHistoryMatch s.history R p (.pushCAS v node s.head) := by
      have h := hpm p; rw [htp] at h; exact h
    refine ⟨spine, R, S_calls, hsp', ?_, by rw [hvals']; exact heval, hR_resp,
      procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
    refine
      { own_lt := fun q n hq => by
          rw [List.length_set]; exact hnode.own_lt q n ((hown_iff q n).mp hq)
        own_not_spine := fun q n hq => hnode.own_not_spine q n ((hown_iff q n).mp hq)
        own_uniq := fun q₁ q₂ n h₁ h₂ =>
          hnode.own_uniq q₁ q₂ n ((hown_iff q₁ n).mp h₁) ((hown_iff q₂ n).mp h₂)
        pushCAS_nd := ?_
        popNext_ok := ?_
        popCAS_ok := ?_ }
    · intro q w n exp hq
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, TreiberPhase.pushCAS.injEq] at hq
        obtain ⟨rfl, rfl, rfl⟩ := hq
        exact List.getElem?_set_self hnode_lt
      · simp only [Function.update_of_ne hqp] at hq
        have hq_own : (s.threads q).OwnsNode n := by rw [hq]; rfl
        have hne_n : node ≠ n := fun h => by
          subst h; exact hqp (hnode.own_uniq q p node hq_own hp_own)
        rw [List.getElem?_set_ne hne_n]
        exact hnode.pushCAS_nd q w n exp hq
    · intro q top hq
      have hqp : q ≠ p := fun h => by subst h; simp only [Function.update_self, reduceCtorEq] at hq
      simp only [Function.update_of_ne hqp] at hq
      obtain ⟨hlt, hno⟩ := hnode.popNext_ok q top hq
      exact ⟨by rw [List.length_set]; exact hlt, fun r hr => hno r ((hown_iff r top).mp hr)⟩
    · intro q top nxt val hq
      have hqp : q ≠ p := fun h => by subst h; simp only [Function.update_self, reduceCtorEq] at hq
      simp only [Function.update_of_ne hqp] at hq
      obtain ⟨hlt, hno, hnd⟩ := hnode.popCAS_ok q top nxt val hq
      have hne_top : node ≠ top := fun h => by subst h; exact hno p hp_own
      refine ⟨by rw [List.length_set]; exact hlt,
        fun r hr => hno r ((hown_iff r top).mp hr), ?_⟩
      rw [List.getElem?_set_ne hne_top]; exact hnd
  | pushCAS v node exp =>
    rw [treiberFreshNodeStep, htp]
    by_cases hc : s.head = exp
    · -- LINEARIZATION POINT 1: `pushCAS` succeeds (`s.head = exp`), pushing `node` onto `spine`!
      simp only [hc, ↓reduceIte]
      have hp_own : (s.threads p).OwnsNode node := by rw [htp]; rfl
      have hnode_lt : node < s.heap.length := hnode.own_lt p node hp_own
      have hnd_eq : s.heap[node]? = some ⟨v, exp⟩ := hnode.pushCAS_nd p v node exp htp
      rw [hc] at hsp
      have hsp_new : ValidSpine s.heap (some node) (node :: spine) :=
        ⟨rfl, hnode_lt, ⟨v, exp⟩, hnd_eq, hsp⟩
      have hvals_new : spineVals s.heap (node :: spine) = v :: spineVals s.heap spine := by
        simp only [spineVals, List.filterMap_cons, hnd_eq, Option.map_some]
      have hpm_p := hpm p; rw [htp] at hpm_p
      obtain ⟨hRp_nil, cs_p, hHp⟩ := hpm_p
      obtain ⟨heval', hR₁_resp, hpm', heqS', hprecS'⟩ :=
        linearize_step_witness
          (threads := s.threads)
          (threads' := Function.update s.threads p (.returning .pushAck))
          (stk' := spineVals s.heap (node :: spine))
          heval (by dsimp only [stackStep]; rw [← hvals_new]) hR_resp hpm heqS hprecS hHp hRp_nil
          (Function.update_self _ _ _) (fun q hqp => Function.update_of_ne hqp _ _)
      have hown_sub : ∀ q n,
          (Function.update s.threads p (.returning .pushAck) q).OwnsNode n →
            q ≠ p ∧ (s.threads q).OwnsNode n := by
        intro q n hq
        by_cases hqp : q = p
        · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
        · simp only [Function.update_of_ne hqp] at hq; exact ⟨hqp, hq⟩
      refine ⟨node :: spine, _, _, hsp_new,
        hnode.update_nonSpecial (fun q n hq => (hown_sub q n hq).2) ?_
          (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
        heval', hR₁_resp, hpm', heqS', hprecS'⟩
      intro q n hq hmem
      obtain ⟨hqp, hq_own⟩ := hown_sub q n hq
      rcases List.mem_cons.mp hmem with rfl | hsp_mem
      · exact hqp (hnode.own_uniq q p n hq_own hp_own)
      · exact hnode.own_not_spine q n hq_own hsp_mem
    · -- `pushCAS` fails (`s.head ≠ exp`), retrying from `pushRead v node`.
      simp only [hc, ↓reduceIte]
      have hown_sub : ∀ q n,
          (Function.update s.threads p (.pushRead v node) q).OwnsNode n →
            (s.threads q).OwnsNode n := by
        intro q n hq
        by_cases hqp : q = p
        · subst hqp; simp only [Function.update_self, htp, TreiberPhase.OwnsNode] at hq ⊢; exact hq
        · rwa [Function.update_of_ne hqp] at hq
      have hp_pm : ProcHistoryMatch s.history R p (.pushRead v node) := by
        have h := hpm p; rw [htp] at h; exact h
      exact ⟨spine, R, S_calls, hsp,
        hnode.update_nonSpecial hown_sub (fun q n hq => hnode.own_not_spine q n (hown_sub q n hq))
          (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
        heval, hR_resp, procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
  | popRead =>
    rw [treiberFreshNodeStep, htp]
    cases hh : s.head with
    | none =>
      -- LINEARIZATION POINT 2: `popRead` observes `s.head = none`, linearizing empty `pop → none`!
      dsimp only
      rw [hh] at hsp
      have hsp_nil : spine = [] := by
        cases spine with
        | nil => rfl
        | cons _ _ => exact False.elim hsp
      subst hsp_nil
      have hpm_p := hpm p; rw [htp] at hpm_p
      obtain ⟨hRp_nil, cs_p, hHp⟩ := hpm_p
      obtain ⟨heval', hR₁_resp, hpm', heqS', hprecS'⟩ :=
        linearize_step_witness
          (threads := s.threads)
          (threads' := Function.update s.threads p (.returning (.popRet none)))
          heval rfl hR_resp hpm heqS hprecS hHp hRp_nil
          (Function.update_self _ _ _) (fun q hqp => Function.update_of_ne hqp _ _)
      have hown_sub : ∀ q n,
          (Function.update s.threads p (.returning (.popRet none)) q).OwnsNode n →
            (s.threads q).OwnsNode n := by
        intro q n hq
        by_cases hqp : q = p
        · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
        · rwa [Function.update_of_ne hqp] at hq
      exact ⟨[], _, _, trivial,
        hnode.update_nonSpecial hown_sub (fun _ _ _ hm => List.not_mem_nil hm)
          (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
        heval', hR₁_resp, hpm', heqS', hprecS'⟩
    | some top =>
      -- Nonempty `popRead`: `top ∈ spine`, so `top < s.heap.length` and unowned!
      dsimp only
      rw [hh] at hsp
      have htop_props : top < s.heap.length ∧ top ∈ spine := by
        cases spine with
        | nil => exact False.elim hsp
        | cons hd rest => obtain ⟨rfl, hlt, _⟩ := hsp; exact ⟨hlt, List.mem_cons_self⟩
      have hown_iff : ∀ q n,
          (Function.update s.threads p (.popNext top) q).OwnsNode n ↔
            (s.threads q).OwnsNode n := by
        intro q n
        by_cases hqp : q = p
        · subst hqp; simp only [Function.update_self, htp, TreiberPhase.OwnsNode]
        · simp only [Function.update_of_ne hqp]
      have hp_pm : ProcHistoryMatch s.history R p (.popNext top) := by
        have h := hpm p; rw [htp] at h; exact h
      refine ⟨spine, R, S_calls, hsp, ?_, heval, hR_resp,
        procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
      dsimp only
      refine
        { own_lt := fun q n hq => hnode.own_lt q n ((hown_iff q n).mp hq)
          own_not_spine := fun q n hq => hnode.own_not_spine q n ((hown_iff q n).mp hq)
          own_uniq := fun q₁ q₂ n h₁ h₂ =>
            hnode.own_uniq q₁ q₂ n ((hown_iff q₁ n).mp h₁) ((hown_iff q₂ n).mp h₂)
          pushCAS_nd := fun q w n exp hq => by
            have hqp : q ≠ p := fun h => by
              subst h; simp only [Function.update_self, reduceCtorEq] at hq
            rw [Function.update_of_ne hqp] at hq
            exact hnode.pushCAS_nd q w n exp hq
          popNext_ok := fun q top' hq => by
            by_cases hqp : q = p
            · subst hqp
              simp only [Function.update_self, TreiberPhase.popNext.injEq] at hq
              subst hq
              exact ⟨htop_props.1,
                fun r hr => hnode.own_not_spine r top ((hown_iff r top).mp hr) htop_props.2⟩
            · rw [Function.update_of_ne hqp] at hq
              obtain ⟨hlt, hno⟩ := hnode.popNext_ok q top' hq
              exact ⟨hlt, fun r hr => hno r ((hown_iff r top').mp hr)⟩
          popCAS_ok := fun q top' nxt val hq => by
            have hqp : q ≠ p := fun h => by
              subst h; simp only [Function.update_self, reduceCtorEq] at hq
            rw [Function.update_of_ne hqp] at hq
            obtain ⟨hlt, hno, hnd⟩ := hnode.popCAS_ok q top' nxt val hq
            exact ⟨hlt, fun r hr => hno r ((hown_iff r top').mp hr), hnd⟩ }
  | popNext top =>
    obtain ⟨htop_lt, htop_no⟩ := hnode.popNext_ok p top htp
    have hget : s.heap[top]? = some s.heap[top] := List.getElem?_eq_getElem htop_lt
    rw [treiberFreshNodeStep, htp]
    dsimp only
    rw [hget]
    dsimp only
    have hown_iff : ∀ q n,
        (Function.update s.threads p (.popCAS top s.heap[top].next s.heap[top].val) q).OwnsNode n ↔
          (s.threads q).OwnsNode n := by
      intro q n
      by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, htp, TreiberPhase.OwnsNode]
      · simp only [Function.update_of_ne hqp]
    have hp_pm : ProcHistoryMatch s.history R p (.popCAS top s.heap[top].next s.heap[top].val) := by
      have h := hpm p; rw [htp] at h; exact h
    refine ⟨spine, R, S_calls, hsp, ?_, heval, hR_resp,
      procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
    dsimp only
    refine
      { own_lt := fun q n hq => hnode.own_lt q n ((hown_iff q n).mp hq)
        own_not_spine := fun q n hq => hnode.own_not_spine q n ((hown_iff q n).mp hq)
        own_uniq := fun q₁ q₂ n h₁ h₂ =>
          hnode.own_uniq q₁ q₂ n ((hown_iff q₁ n).mp h₁) ((hown_iff q₂ n).mp h₂)
        pushCAS_nd := fun q w n exp hq => by
          have hqp : q ≠ p := fun h => by
            subst h; simp only [Function.update_self, reduceCtorEq] at hq
          rw [Function.update_of_ne hqp] at hq
          exact hnode.pushCAS_nd q w n exp hq
        popNext_ok := fun q top' hq => by
          have hqp : q ≠ p := fun h => by
            subst h; simp only [Function.update_self, reduceCtorEq] at hq
          rw [Function.update_of_ne hqp] at hq
          obtain ⟨hlt, hno⟩ := hnode.popNext_ok q top' hq
          exact ⟨hlt, fun r hr => hno r ((hown_iff r top').mp hr)⟩
        popCAS_ok := fun q top' nxt val hq => by
          by_cases hqp : q = p
          · subst hqp
            simp only [Function.update_self, TreiberPhase.popCAS.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            refine ⟨htop_lt, fun r hr => htop_no r ((hown_iff r top).mp hr), ?_⟩
            rw [hget]
          · rw [Function.update_of_ne hqp] at hq
            obtain ⟨hlt, hno, hnd⟩ := hnode.popCAS_ok q top' nxt val hq
            exact ⟨hlt, fun r hr => hno r ((hown_iff r top').mp hr), hnd⟩ }
  | popCAS top nxt retVal =>
    rw [treiberFreshNodeStep, htp]
    by_cases hc : s.head = some top
    · -- LINEARIZATION POINT 3: `popCAS` succeeds (`s.head = some top`), popping `top` from `spine`!
      simp only [hc, ↓reduceIte]
      obtain ⟨_, _, hnd_top⟩ := hnode.popCAS_ok p top nxt retVal htp
      rw [hc] at hsp
      cases spine with
      | nil => exact False.elim hsp
      | cons hd rest =>
        obtain ⟨rfl, _, nd, hnd', hsp_rest⟩ := hsp
        rw [hnd_top] at hnd'
        injection hnd' with hnd_eq
        subst hnd_eq
        have hvals_cons : spineVals s.heap (top :: rest) = retVal :: spineVals s.heap rest := by
          simp only [spineVals, List.filterMap_cons, hnd_top, Option.map_some]
        have hpm_p := hpm p; rw [htp] at hpm_p
        obtain ⟨hRp_nil, cs_p, hHp⟩ := hpm_p
        obtain ⟨heval', hR₁_resp, hpm', heqS', hprecS'⟩ :=
          linearize_step_witness
            (threads := s.threads)
            (threads' := Function.update s.threads p (.returning (.popRet (some retVal))))
            heval (by rw [hvals_cons]; rfl) hR_resp hpm heqS hprecS hHp hRp_nil
            (Function.update_self _ _ _) (fun q hqp => Function.update_of_ne hqp _ _)
        have hown_sub : ∀ q n,
            (Function.update s.threads p (.returning (.popRet (some retVal))) q).OwnsNode n →
              (s.threads q).OwnsNode n := by
          intro q n hq
          by_cases hqp : q = p
          · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
          · rwa [Function.update_of_ne hqp] at hq
        exact ⟨rest, _, _, hsp_rest,
          hnode.update_nonSpecial hown_sub
            (fun q n hq hm => hnode.own_not_spine q n (hown_sub q n hq) (List.mem_cons_of_mem _ hm))
            (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
          heval', hR₁_resp, hpm', heqS', hprecS'⟩
    · -- `popCAS` fails (`s.head ≠ some top`), retrying from `popRead`.
      simp only [hc, ↓reduceIte]
      have hown_sub : ∀ q n,
          (Function.update s.threads p .popRead q).OwnsNode n → (s.threads q).OwnsNode n := by
        intro q n hq
        by_cases hqp : q = p
        · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
        · rwa [Function.update_of_ne hqp] at hq
      have hp_pm : ProcHistoryMatch s.history R p .popRead := by
        have h := hpm p; rw [htp] at h; exact h
      exact ⟨spine, R, S_calls, hsp,
        hnode.update_nonSpecial hown_sub (fun q n hq => hnode.own_not_spine q n (hown_sub q n hq))
          (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
        heval, hR_resp, procHistoryMatch_update_same hpm hp_pm, heqS, hprecS⟩
  | returning resp =>
    -- Return step: move `.resp p () resp` from `R` into `s.history ++ [.resp p () resp]`.
    rw [treiberFreshNodeStep, htp]
    dsimp only
    have hwf' := wellFormed_of_procHistoryMatch hpm
    have hpm_p := hpm p; rw [htp] at hpm_p
    obtain ⟨hRp_eq, cs_p, op_p, hHp⟩ := hpm_p
    obtain ⟨hR'_resp, _, _, heq_fl, hprec_fl⟩ :=
      History.flush_resp_from_extension hR_resp hwf' heqS hprecS hRp_eq
    have hown_sub : ∀ q n,
        (Function.update s.threads p .idle q).OwnsNode n → (s.threads q).OwnsNode n := by
      intro q n hq
      by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, TreiberPhase.OwnsNode] at hq
      · rwa [Function.update_of_ne hqp] at hq
    refine ⟨spine, _, S_calls, hsp,
      hnode.update_nonSpecial hown_sub (fun q n hq => hnode.own_not_spine q n (hown_sub q n hq))
        (fun _ _ _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h),
      heval, hR'_resp, ?_, heq_fl, hprec_fl⟩
    intro q
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, ProcHistoryMatch]
      have hR'_p :
          History.procSubhistory (R.filter fun e => decide (e.proc ≠ q)) q = [] := by
        rw [History.procSubhistory, List.filter_filter, List.filter_eq_nil_iff]
        intro e _ hboth
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hboth
        exact (of_decide_eq_true h2) (of_decide_eq_true h1)
      refine ⟨hR'_p, cs_p ++ [⟨q, (), op_p, resp⟩], ?_⟩
      simp only [History.procSubhistory_append, hHp, History.procSubhistory_cons,
        Event.proc_resp, ↓reduceIte, History.procSubhistory_nil, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, OpCall.toEvents,
        List.append_assoc, List.cons_append, List.nil_append]
    · simp only [Function.update_of_ne hqp]
      have hHq : History.procSubhistory (s.history ++ [.resp p () resp]) q =
          History.procSubhistory s.history q := by
        simp only [History.procSubhistory_append, History.procSubhistory_cons, Event.proc_resp,
          Ne.symm hqp, ↓reduceIte, History.procSubhistory_nil, List.append_nil]
      have hR'_q :
          History.procSubhistory (R.filter fun e => decide (e.proc ≠ p)) q =
            History.procSubhistory R q := by
        simp only [History.procSubhistory, List.filter_filter]
        refine congrArg (List.filter · R) (funext fun e => ?_)
        by_cases heq_q : e.proc = q
        · simp only [heq_q, decide_eq_true hqp, Bool.and_true]
        · simp only [heq_q, decide_false, Bool.false_and]
      exact procHistoryMatch_congr hHq hR'_q (hpm q)

private theorem treiberInv_of_reachable {P V : Type u} [DecidableEq P]
    {s : TreiberFreshNodeState P V} (hs : (treiberFreshNodeSystem P V).Reachable s) :
    TreiberInv s := by
  refine ProgressSystem.Reachable.induction (treiberInv_init P V) ?_ hs
  intro s₁ lbl s₂ _ htr hinv
  cases lbl with
  | invoke p => exact treiberInv_invoke hinv htr
  | exec p done =>
    obtain ⟨hact, hstep⟩ := htr
    have hs₂ : (treiberFreshNodeStep s₁ p).1 = s₂ := congrArg Prod.fst hstep
    rw [← hs₂]
    exact treiberInv_exec hinv hact

end LinearizabilityProof

/-- Fresh-node model step for #7501, not the cited endpoint (after [Treiber1986];
[Hendler, Shavit, and Yerushalmi, §5, Lemma 5.13, p. 214][HendlerShavitYerushalmi2004]): for every
reachable configuration `s` of `treiberFreshNodeSystem P V`, the recorded concurrent history
`s.history` is linearizable with respect to the sequential LIFO stack specification
`stackSeqSpec V`, leaving the ABA version-tagged free-list recycling model open in #7501. -/
theorem treiberFreshNode_isLinearizable {P V : Type u} [DecidableEq P]
    {s : TreiberFreshNodeState P V} (hs : (treiberFreshNodeSystem P V).Reachable s) :
    IsLinearizable (fun _ : Unit => stackSeqSpec V) s.history := by
  obtain ⟨spine, R, S_calls, _, _, heval, hR_resp, hpm, heqS, hprecS⟩ :=
    treiberInv_of_reachable hs
  have hwf' := wellFormed_of_procHistoryMatch hpm
  let S := S_calls.flatMap OpCall.toEvents
  refine ⟨s.history ++ R, ⟨R, hR_resp, rfl, hwf'⟩, S,
    History.isSequential_flatMap_toEvents S_calls, ?_, heqS, hprecS⟩
  intro u
  cases u
  have hall_u : ∀ e ∈ S, e.obj = () := fun _ _ => rfl
  rw [History.objSubhistory_eq_self_of_forall_obj hall_u]
  simp only [stackSeqSpec, SeqSpec.mem_ofMachine_allowed]
  exact evalStack_mem_allowed heval

end Cslib.Distributed.ConcurrentObjects
