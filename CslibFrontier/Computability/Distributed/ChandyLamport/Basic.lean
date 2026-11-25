/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Asynchronous point-to-point FIFO message-passing networks

This module models asynchronous distributed systems communicating over point-to-point first-in,
first-out (FIFO) channels along a directed communication graph `Digraph P`, following the underlying
system model of [ChandyLamport1985] (§2, pp. 65–68, and §1, p. 64 for stable properties).

Each ordered pair `(src, dest)` of processes has an unbounded reliable FIFO queue
`chan src dest : List M` whose head is the next message deliverable to `dest` and whose tail
receives newly sent messages via append. Where §2 (p. 66, Figure 1) allows parallel labeled
channels and single-channel 5-tuple events `⟨p, s, s', M, c⟩` over finite process/channel sets,
`System P S M` over `Digraph P` models at most one channel per ordered pair (including self-loops),
leaves `P S M : Type*` unrestricted, and allows each step to emit a list `sent : List (P × M)` of
outgoing messages atomically:

* a directed communication graph `graph : Digraph P`,
* allowed spontaneous internal/send steps `internal p st st' sent` at process `p`, and
* allowed message-receive steps `recv src dest st msg st' sent` at `dest` consuming `msg` from the
  head of `chan src dest`.

Both local transition relations may be nondeterministic, while the induced labelled transition
system `System.lts` over `Event P S M` is deterministic given the event label (`lts_deterministic`).
Because `System.lts` includes no artificial stuttering transition, `sys.lts.IsTerminal` expresses
genuine global deadlock or termination, which is automatically a stable global predicate
(`isStablePred_isTerminal`).

The fundamental FIFO queue commutation property (`System.tr_comm_of_ne`) shows that two transitions
at distinct processes `p ≠ q` commute in `sys.lts` whenever the second step does not pop from an
initially empty channel `(p, q)`—because head-pop and tail-append commute on every non-empty list
(`(h :: t) ++ out = h :: (t ++ out)`).

## Main definitions

* `Cslib.Distributed.ChandyLamport.GlobalState`: global configuration consisting of local states
  `proc : P → S` and FIFO channels `chan : P → P → List M`.
* `Cslib.Distributed.ChandyLamport.outgoingTo`: filter outgoing `(dest, m)` pairs addressed to a
  given destination while preserving send order.
* `Cslib.Distributed.ChandyLamport.Event`: transition labels (`internal` and `recv`) of an
  asynchronous FIFO network.
* `Cslib.Distributed.ChandyLamport.GlobalState.applyEvent`,
  `Cslib.Distributed.ChandyLamport.GlobalState.runEvents`: single-event and multi-event state
  transitions induced by `Event`.
* `Cslib.Distributed.ChandyLamport.System`: asynchronous message-passing system over a `Digraph P`.
* `Cslib.Distributed.ChandyLamport.System.lts`,
  `Cslib.Distributed.ChandyLamport.System.validTrace`: labelled transition system (`Cslib.LTS`) of a
  `System` and its executable multi-step trace predicate.
* `Cslib.Distributed.ChandyLamport.System.WellFormedChan`: invariant stating that non-edges carry
  empty channels.
* `Cslib.Distributed.ChandyLamport.IsStablePred`: global state predicates closed under transitions
  of `sys.lts` (such as deadlock, termination, garbage collection, or token bounds).

## Main results

* `Cslib.Distributed.ChandyLamport.System.mTr_iff_validTrace`: finite executions of `sys.lts` match
  `validTrace` + `GlobalState.runEvents`.
* `Cslib.Distributed.ChandyLamport.System.wellFormedChan_mTr`: channel well-formedness is preserved
  across finite executions.
* `Cslib.Distributed.ChandyLamport.System.tr_comm_of_ne`: transitions at distinct processes `p ≠ q`
  commute in `sys.lts` whenever the second transition does not pop from an initially empty channel
  `(p, q)`.
* `Cslib.Distributed.ChandyLamport.isStablePred_isTerminal`: global deadlock/termination
  (`sys.lts.IsTerminal`) is a stable predicate.

## References

* [K. M. Chandy, L. Lamport, *Distributed Snapshots: Determining Global States of Distributed
  Systems*][ChandyLamport1985]
-/

public section

namespace Cslib.Distributed.ChandyLamport

open Cslib

/-- Global configuration of an asynchronous point-to-point FIFO message-passing network. -/
@[ext]
structure GlobalState (P S M : Type*) where
  /-- Local state of each process. -/
  proc : P → S
  /-- Point-to-point FIFO channel `chan src dest`: the head is the next deliverable message and
  newly sent messages are appended to the tail. -/
  chan : P → P → List M

instance instDecidableEqGlobalState {P S M : Type*} [Fintype P] [DecidableEq S] [DecidableEq M] :
    DecidableEq (GlobalState P S M) := fun s₁ s₂ =>
  decidable_of_iff (s₁.proc = s₂.proc ∧ s₁.chan = s₂.chan)
    ⟨fun ⟨hp, hc⟩ => GlobalState.ext hp hc, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Extract the payloads addressed to `dest` from an outgoing list of `(recipient, payload)` pairs,
preserving emission order. -/
@[expose] def outgoingTo {P M : Type*} [DecidableEq P]
    (sent : List (P × M)) (dest : P) : List M :=
  sent.filterMap fun (q, m) => if q = dest then some m else none

@[simp]
theorem outgoingTo_nil {P M : Type*} [DecidableEq P] (dest : P) :
    outgoingTo ([] : List (P × M)) dest = [] := rfl

/-- Payload `m` appears in `outgoingTo sent dest` if and only if `(dest, m) ∈ sent`. -/
@[simp]
theorem mem_outgoingTo_iff {P M : Type*} [DecidableEq P] {sent : List (P × M)} {dest : P} {m : M} :
    m ∈ outgoingTo sent dest ↔ (dest, m) ∈ sent := by
  simp [outgoingTo]

/-- `outgoingTo sent dest` is empty when no entry of `sent` targets `dest`. -/
theorem outgoingTo_eq_nil_of_forall_ne {P M : Type*} [DecidableEq P]
    {sent : List (P × M)} {dest : P} (h : ∀ m, (dest, m) ∉ sent) :
    outgoingTo sent dest = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro m hm
  exact h m (mem_outgoingTo_iff.mp hm)

/-- Pop the head message from channel `(src, dest)`, leaving all other channels and all local
process states unchanged. -/
@[expose] def GlobalState.popChan {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) (src dest : P) : GlobalState P S M where
  proc := s.proc
  chan u v := if u = src ∧ v = dest then (s.chan u v).tail else s.chan u v

/-- Update process `p`'s local state to `nextState` and append its outgoing messages `sent` to the
tails of the corresponding outgoing channels `(p, v)`. -/
@[expose] def GlobalState.applyLocal {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) (p : P) (nextState : S) (sent : List (P × M)) :
    GlobalState P S M where
  proc r := if r = p then nextState else s.proc r
  chan u v := if u = p then s.chan u v ++ outgoingTo sent v else s.chan u v

/-- Transition label of an asynchronous FIFO message-passing system. -/
inductive Event (P S M : Type*) where
  /-- Spontaneous internal/send transition at process `p` moving to `nextState` and emitting
  `sent`. -/
  | internal (p : P) (nextState : S) (sent : List (P × M))
  /-- Receipt of `msg` from the head of channel `(src, dest)` by `dest`, moving `dest` to
  `nextState` and emitting `sent`. -/
  | recv (src dest : P) (msg : M) (nextState : S) (sent : List (P × M))
  deriving @[expose] DecidableEq

/-- The acting process of an `Event`. -/
@[expose] def Event.actor {P S M : Type*} : Event P S M → P
  | .internal p _ _ => p
  | .recv _ dest _ _ _ => dest

/-- Target local state written to `e.actor` by `e`. -/
@[expose] def Event.nextState {P S M : Type*} : Event P S M → S
  | .internal _ st' _ => st'
  | .recv _ _ _ st' _ => st'

/-- Outgoing `(recipient, payload)` list emitted by an `Event`. -/
@[expose] def Event.sent {P S M : Type*} : Event P S M → List (P × M)
  | .internal _ _ sent => sent
  | .recv _ _ _ _ sent => sent

/-- Whether event `e` consumes a message from channel `(src, dest)`. -/
@[expose] def Event.popsFrom {P S M : Type*} (e : Event P S M) (src dest : P) : Prop :=
  match e with
  | .internal _ _ _ => False
  | .recv s d _ _ _ => src = s ∧ dest = d

instance instDecidablePopsFrom {P S M : Type*} [DecidableEq P]
    (e : Event P S M) (src dest : P) : Decidable (e.popsFrom src dest) := by
  cases e with
  | internal _ _ _ => exact isFalse id
  | recv _ _ _ _ _ => exact inferInstanceAs (Decidable (_ ∧ _))

theorem Event.popsFrom_dest {P S M : Type*} {e : Event P S M} {u v : P}
    (h : e.popsFrom u v) : v = e.actor := by
  cases e with
  | internal _ _ _ => exact False.elim h
  | recv _ _ _ _ _ => exact h.2

/-- Next global state obtained by applying event `e` to `s`. -/
@[expose] def GlobalState.applyEvent {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) : Event P S M → GlobalState P S M
  | .internal p st' sent => s.applyLocal p st' sent
  | .recv src dest _ st' sent => (s.popChan src dest).applyLocal dest st' sent

/-- State reached from `s` by applying each event in `xl` sequentially. -/
@[expose] def GlobalState.runEvents {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) : List (Event P S M) → GlobalState P S M
  | [] => s
  | e :: xl => (s.applyEvent e).runEvents xl

theorem GlobalState.applyEvent_proc {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) (e : Event P S M) (r : P) :
    (s.applyEvent e).proc r = if r = e.actor then e.nextState else s.proc r := by
  cases e <;> rfl

theorem GlobalState.applyEvent_chan {P S M : Type*} [DecidableEq P]
    (s : GlobalState P S M) (e : Event P S M) (u v : P) :
    (s.applyEvent e).chan u v =
      (if e.popsFrom u v then (s.chan u v).tail else s.chan u v) ++
        if u = e.actor then outgoingTo e.sent v else [] := by
  cases e with
  | internal p st' sent =>
    simp only [applyEvent, applyLocal, Event.popsFrom, ↓reduceIte, Event.actor, Event.sent]
    by_cases hu : u = p <;> simp [hu]
  | recv src dest msg st' sent =>
    simp only [applyEvent, applyLocal, popChan, Event.popsFrom, Event.actor, Event.sent]
    by_cases hu : u = dest
    · subst hu
      by_cases hp : u = src ∧ v = u <;> simp [hp]
    · simp only [hu, ↓reduceIte, List.append_nil]
      congr 1

/-- Underlying asynchronous message-passing system over a directed communication graph `Digraph P`.
Both spontaneous steps (`internal`) and message-receive steps (`recv`) may be relational
(nondeterministic). -/
structure System (P S M : Type*) where
  /-- Directed communication topology: channel `(u, v)` exists when `graph.Adj u v`. -/
  graph : Digraph P
  /-- Allowed spontaneous transitions `internal p st st' sent` at process `p`. -/
  internal : P → S → S → List (P × M) → Prop
  /-- Allowed receive transitions `recv src dest st msg st' sent` at process `dest`. -/
  recv : P → P → S → M → S → List (P × M) → Prop

namespace System

variable {P S M : Type*} (sys : System P S M)

/-- Whether event `e` is enabled in global state `s`. -/
@[expose] def Enabled (s : GlobalState P S M) : Event P S M → Prop
  | .internal p st' sent =>
    sys.internal p (s.proc p) st' sent ∧
    ∀ rm ∈ sent, sys.graph.Adj p rm.1
  | .recv src dest msg st' sent =>
    sys.graph.Adj src dest ∧
    (s.chan src dest).head? = some msg ∧
    sys.recv src dest (s.proc dest) msg st' sent ∧
    ∀ rm ∈ sent, sys.graph.Adj dest rm.1

instance instDecidableEnabled [DecidableEq M] [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (s : GlobalState P S M) (e : Event P S M) : Decidable (sys.Enabled s e) := by
  cases e <;> exact inferInstanceAs (Decidable (_ ∧ _))

/-- Labelled transition system of `sys` with FIFO point-to-point channels. -/
@[expose] def lts [DecidableEq P] : LTS (GlobalState P S M) (Event P S M) where
  Tr s e s' := sys.Enabled s e ∧ s' = s.applyEvent e

/-- `sys.lts` is deterministic: each state and `Event` label determines at most one successor. -/
instance lts_deterministic [DecidableEq P] : sys.lts.Deterministic where
  deterministic _ _ _ _ h₁ h₂ := h₁.2.trans h₂.2.symm

/-- Executable trace-validity predicate checking that each event in `xl` is enabled when reached
from `s`. -/
@[expose] def validTrace [DecidableEq P] (s : GlobalState P S M) : List (Event P S M) → Prop
  | [] => True
  | e :: xl => sys.Enabled s e ∧ validTrace (s.applyEvent e) xl

instance instDecidableValidTrace [DecidableEq P] [DecidableEq M] [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (s : GlobalState P S M) (xl : List (Event P S M)) : Decidable (sys.validTrace s xl) := by
  induction xl generalizing s with
  | nil => exact isTrue trivial
  | cons e xl ih =>
    have := ih (s.applyEvent e)
    exact inferInstanceAs (Decidable (_ ∧ _))

/-- Because `sys.lts` is deterministic, `sys.lts.MTr s xl s'` holds if and only if `xl` is a valid
trace from `s` and `s' = s.runEvents xl`. -/
theorem mTr_iff_validTrace [DecidableEq P] {s s' : GlobalState P S M} {xl : List (Event P S M)} :
    sys.lts.MTr s xl s' ↔ sys.validTrace s xl ∧ s' = s.runEvents xl := by
  induction xl generalizing s with
  | nil =>
    constructor
    · rintro ⟨⟩
      exact ⟨trivial, rfl⟩
    · rintro ⟨_, rfl⟩
      exact .refl
  | cons e xl ih =>
    constructor
    · rintro (_ | ⟨⟨hen, rfl⟩, hrest⟩)
      obtain ⟨hv, hr⟩ := ih.mp hrest
      exact ⟨⟨hen, hv⟩, hr⟩
    · rintro ⟨⟨hen, hv⟩, rfl⟩
      exact .stepL ⟨hen, rfl⟩ (ih.mpr ⟨hv, rfl⟩)

instance instDecidableMTr [Fintype P] [DecidableEq P] [DecidableEq S] [DecidableEq M]
    [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (s s' : GlobalState P S M) (xl : List (Event P S M)) : Decidable (sys.lts.MTr s xl s') :=
  decidable_of_iff (sys.validTrace s xl ∧ s' = s.runEvents xl) sys.mTr_iff_validTrace.symm

private lemma enabled_sent_adj {s : GlobalState P S M} {e : Event P S M}
    (hen : sys.Enabled s e) : ∀ rm ∈ e.sent, sys.graph.Adj e.actor rm.1 := by
  cases e with
  | internal _ _ _ => exact hen.2
  | recv _ _ _ _ _ => exact hen.2.2.2

private lemma enabled_pop_nonempty {s : GlobalState P S M} {e : Event P S M} {u v : P}
    (hen : sys.Enabled s e) (hp : e.popsFrom u v) : s.chan u v ≠ [] := by
  cases e with
  | internal _ _ _ => exact False.elim hp
  | recv src dest msg _ _ =>
    rcases hp with ⟨rfl, rfl⟩
    obtain ⟨_, ht⟩ := List.head?_eq_some_iff.mp hen.2.1
    simp [ht]

/-- A global state has well-formed channels if every non-edge of `sys.graph` is empty. -/
@[expose] def WellFormedChan (s : GlobalState P S M) : Prop :=
  ∀ u v, ¬ sys.graph.Adj u v → s.chan u v = []

instance instDecidableWellFormedChan [Fintype P] [DecidableRel sys.graph.Adj]
    (s : GlobalState P S M) : Decidable (sys.WellFormedChan s) :=
  inferInstanceAs (Decidable (∀ _ _, _))

private theorem wellFormedChan_tr [DecidableEq P] : sys.lts.TrInv sys.WellFormedChan := by
  rintro s e _ ⟨hen, rfl⟩ hwf u v huv
  rw [GlobalState.applyEvent_chan, hwf u v huv]
  by_cases hu : u = e.actor
  · subst hu
    have hout : outgoingTo e.sent v = [] :=
      outgoingTo_eq_nil_of_forall_ne fun m hm => huv (sys.enabled_sent_adj hen (v, m) hm)
    simp [hout]
  · simp [hu]

/-- Non-edge channels remain empty across any finite execution of `sys.lts`. -/
theorem wellFormedChan_mTr [DecidableEq P] {s₁ s₂ : GlobalState P S M} {xl : List (Event P S M)}
    (hmtr : sys.lts.MTr s₁ xl s₂) (hwf : sys.WellFormedChan s₁) : sys.WellFormedChan s₂ :=
  LTS.mtrInv_of_trInv sys.wellFormedChan_tr s₁ xl s₂ hmtr hwf

/-- **FIFO causal commutation for distinct processes:** if `e₁` (at actor `p`) is followed by `e₂`
(at actor `q ≠ p`), and `e₂` does not pop from an initially empty channel `(p, q)` in `s`, then
`e₂` is already enabled in `s` and executing `e₂` before `e₁` reaches the exact same state `s₂`. -/
theorem tr_comm_of_ne [DecidableEq P] {s s₁ s₂ : GlobalState P S M} {e₁ e₂ : Event P S M}
    (htr₁ : sys.lts.Tr s e₁ s₁) (htr₂ : sys.lts.Tr s₁ e₂ s₂)
    (hne : e₁.actor ≠ e₂.actor)
    (hchan : e₂.popsFrom e₁.actor e₂.actor → s.chan e₁.actor e₂.actor ≠ []) :
    ∃ s₁', sys.lts.Tr s e₂ s₁' ∧ sys.lts.Tr s₁' e₁ s₂ := by
  obtain ⟨hen₁, rfl⟩ := htr₁
  obtain ⟨hen₂, rfl⟩ := htr₂
  refine ⟨s.applyEvent e₂, ⟨?_, rfl⟩, ⟨?_, ?_⟩⟩
  · -- Enabledness of `e₂` at `s`
    have hproc₂ : (s.applyEvent e₁).proc e₂.actor = s.proc e₂.actor := by
      simp [GlobalState.applyEvent_proc, hne.symm]
    cases e₂ with
    | internal q st₂' sent₂ =>
      simp only [Event.actor] at hproc₂
      simp only [Enabled] at hen₂ ⊢
      rwa [← hproc₂]
    | recv src₂ q msg₂ st₂' sent₂ =>
      simp only [Event.actor] at hproc₂ hne
      simp only [Enabled] at hen₂ ⊢
      refine ⟨hen₂.1, ?_, hproc₂ ▸ hen₂.2.2.1, hen₂.2.2.2⟩
      have hnp₁ : ¬ e₁.popsFrom src₂ q := fun hp => hne (e₁.popsFrom_dest hp).symm
      have hhead := hen₂.2.1
      simp only [GlobalState.applyEvent_chan, hnp₁, ↓reduceIte] at hhead
      by_cases hsrc₂ : src₂ = e₁.actor
      · subst hsrc₂
        have hne₀ : s.chan e₁.actor q ≠ [] := hchan ⟨rfl, rfl⟩
        obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil hne₀
        simpa [hht] using hhead
      · simpa [hsrc₂] using hhead
  · -- Enabledness of `e₁` at `s.applyEvent e₂`
    have hproc₁ : (s.applyEvent e₂).proc e₁.actor = s.proc e₁.actor := by
      simp [GlobalState.applyEvent_proc, hne]
    cases e₁ with
    | internal p st₁' sent₁ =>
      simp only [Event.actor] at hproc₁
      simp only [Enabled] at hen₁ ⊢
      rwa [hproc₁]
    | recv src₁ p msg₁ st₁' sent₁ =>
      simp only [Event.actor] at hproc₁ hne
      simp only [Enabled] at hen₁ ⊢
      refine ⟨hen₁.1, ?_, hproc₁.symm ▸ hen₁.2.2.1, hen₁.2.2.2⟩
      have hnp₂ : ¬ e₂.popsFrom src₁ p := fun hp => hne (e₂.popsFrom_dest hp)
      obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hen₁.2.1
      rw [GlobalState.applyEvent_chan]
      simp only [hnp₂, ↓reduceIte, ht]
      by_cases hu : src₁ = e₂.actor <;> simp [hu]
  · -- Pointwise global-state equality
    apply GlobalState.ext
    · funext r
      simp only [GlobalState.applyEvent_proc]
      by_cases hr₁ : r = e₁.actor <;> by_cases hr₂ : r = e₂.actor <;> simp_all
    · funext u v
      simp only [GlobalState.applyEvent_chan]
      by_cases hp₁ : e₁.popsFrom u v
      · have hp₂ : ¬ e₂.popsFrom u v := fun hp₂ =>
          hne ((e₁.popsFrom_dest hp₁).symm.trans (e₂.popsFrom_dest hp₂))
        obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil (sys.enabled_pop_nonempty hen₁ hp₁)
        simp only [hp₁, hp₂, ↓reduceIte, hht, List.tail_cons]
        by_cases hu₁ : u = e₁.actor <;> by_cases hu₂ : u = e₂.actor <;> simp_all
      · by_cases hp₂ : e₂.popsFrom u v
        · obtain rfl := e₂.popsFrom_dest hp₂
          simp only [hp₁, hp₂, ↓reduceIte]
          by_cases hu₁ : u = e₁.actor
          · subst hu₁
            obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil (hchan hp₂)
            simp [hne, hht]
          · by_cases hu₂ : u = e₂.actor <;> simp_all
        · simp only [hp₁, hp₂, ↓reduceIte]
          by_cases hu₁ : u = e₁.actor <;> by_cases hu₂ : u = e₂.actor <;> simp_all

end System

/-! ### Stable global predicates -/

/-- A global predicate `Φ` is *stable* for `sys` if once `Φ` holds in a state `s`, it continues to
hold in every successor state `s'` of `sys.lts` ([ChandyLamport1985], §1, p. 64, equivalent via
`IsStablePred.canReach` to closure under reachability). Standard examples include deadlock,
computation termination, and loss of all tokens in a token ring. -/
@[expose] def IsStablePred {P S M : Type*} [DecidableEq P]
    (sys : System P S M) (Φ : GlobalState P S M → Prop) : Prop :=
  ∀ s a s', sys.lts.Tr s a s' → Φ s → Φ s'

/-- A stable predicate persists across arbitrary finite executions (`CanReach`). -/
theorem IsStablePred.canReach {P S M : Type*} [DecidableEq P] {sys : System P S M}
    {Φ : GlobalState P S M → Prop} (hΦ : IsStablePred sys Φ)
    {s₁ s₂ : GlobalState P S M} (hr : sys.lts.CanReach s₁ s₂) (hs : Φ s₁) : Φ s₂ := by
  obtain ⟨xl, hxl⟩ := hr
  exact LTS.mtrInv_of_trInv hΦ s₁ xl s₂ hxl hs

/-- Contrapositive backward transfer: if a stable predicate fails at a reachable state `s₂`, it was
already false at `s₁`. -/
theorem IsStablePred.not_of_canReach {P S M : Type*} [DecidableEq P] {sys : System P S M}
    {Φ : GlobalState P S M → Prop} (hΦ : IsStablePred sys Φ)
    {s₁ s₂ : GlobalState P S M} (hr : sys.lts.CanReach s₁ s₂) (hnot : ¬ Φ s₂) : ¬ Φ s₁ :=
  fun hs => hnot (hΦ.canReach hr hs)

/-- Global deadlock/termination (`sys.lts.IsTerminal`) is a stable predicate. -/
theorem isStablePred_isTerminal {P S M : Type*} [DecidableEq P] (sys : System P S M) :
    IsStablePred sys sys.lts.IsTerminal :=
  fun _ a s' htr hterm => False.elim (hterm a s' htr)

end Cslib.Distributed.ChandyLamport
