/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Function.Basic

/-!
# Asynchronous diffusing computations and the Dijkstra–Scholten overlay

This module models asynchronous diffusing computations and the single-parent message-passing
termination-detection overlay as a milestone step toward `#7286`, after [DijkstraScholten1980]
(inspected in author manuscript `EWD687a`, `EWD687a - 0`–`5`, PDF pp. 3–8).

Given a process type `P` and a distinguished initiator `root : P`, a global `State P` is completely
ghost-free:

* each process `p : P` stores only `ProcState P`: `active : Bool`, `deficit : ℕ` (outgoing
  unacknowledged basic-message count `D` in `EWD687a - 2`, PDF p. 5), and `parent : Option P`
  (incoming engagement-tree pointer);
* `basicMsgs : Multiset (BasicMsg P)` holds unordered in-flight basic messages `⟨src, dst⟩`;
* `signals : Multiset P` holds unordered in-flight acknowledgement signals addressed to their
  recipient `p : P` (matching `EWD687a - 5`, PDF p. 8: recipients need not distinguish which
  successor emitted a signal).

Compared with `EWD687a`'s abstract directed-graph formulation (atomic edge-deficit updates, no
incoming edges at the environment, and arbitrary "cornet" pointed bags deferring non-engagement
signals subject to guard `G`), `lts root` models asynchronous in-flight packets and the concrete
single-parent eager-acknowledgement policy:

1. `Action.sendBasic src dst`: an active process `src` emits basic message `⟨src, dst⟩` and
   increments `deficit src`.
2. `Action.recvBasic src dst`: delivering `⟨src, dst⟩ ∈ basicMsgs` sets `active dst := true`. If
   `dst ≠ root` and `parent dst = none`, `dst` attaches to the engagement tree via
   `parent dst := some src`; otherwise (`dst = root` or `dst` is already engaged in the tree),
   `dst` keeps its existing `parent` and immediately emits a `signal` to `src`.
3. `Action.becomeIdle p`: an active process `p` turns `active p := false`.
4. `Action.recvSignal p`: delivering an in-flight signal `p ∈ signals` decrements `deficit p`.
5. `Action.detach p q`: an idle non-root process `p ≠ root` with `deficit p = 0` and
   `parent p = some q` detaches (`parent p := none`) and emits a `signal` to `q`.

`root` detects termination (`State.Terminated root`) when `active root = false ∧ deficit root = 0`.
Both the labelled transition system `lts root` and multi-step execution `runTrace? root` share one
executable transition function `step? root`, enabling kernel `decide` trace verification.

## Main definitions

* `Cslib.Distributed.DijkstraScholten.ProcState`: ghost-free local process state
  (`active`, `deficit`, `parent`).
* `Cslib.Distributed.DijkstraScholten.BasicMsg`: point-to-point basic message `⟨src, dst⟩`.
* `Cslib.Distributed.DijkstraScholten.State`: global asynchronous configuration.
* `Cslib.Distributed.DijkstraScholten.initState`: initial diffusing configuration with only `root`
  active and empty channels.
* `Cslib.Distributed.DijkstraScholten.Action`: LTS transition labels (`sendBasic`, `recvBasic`,
  `becomeIdle`, `recvSignal`, `detach`).
* `Cslib.Distributed.DijkstraScholten.step?`, `Cslib.Distributed.DijkstraScholten.runTrace?`:
  executable single-step and multi-step transition evaluators.
* `Cslib.Distributed.DijkstraScholten.lts`,
  `Cslib.Distributed.DijkstraScholten.deterministic_lts`: deterministic `Cslib.LTS` for the
  Dijkstra–Scholten overlay.
* `Cslib.Distributed.DijkstraScholten.Reachable`: reachability from `initState root` in `lts root`.
* `Cslib.Distributed.DijkstraScholten.State.Terminated`: local root termination predicate
  (`active root = false ∧ deficit root = 0`).
* `Cslib.Distributed.DijkstraScholten.State.GlobalQuiescent`: global quiescence (all processes
  idle with zero deficit and `parent = none`, and no basic or signal packets in flight).
* `Cslib.Distributed.DijkstraScholten.State.ComputationIdle`: underlying diffusing computation has
  ceased (`∀ p, active p = false` and `basicMsgs = 0`), while control signals/detachments may
  still be draining.

## Main results

* `Cslib.Distributed.DijkstraScholten.mtr_iff_runTrace?_eq_some`: multi-step transitions in
  `lts root` coincide with `runTrace? root s tr = some s'`.

## References

* [E. W. Dijkstra, C. S. Scholten,
  *Termination Detection for Diffusing Computations*][DijkstraScholten1980]
-/

public section

namespace Cslib.Distributed.DijkstraScholten

open Cslib

/-- Ghost-free local state of a process in the Dijkstra–Scholten overlay (`EWD687a - 2`–`5`,
PDF pp. 5–8): `active` status in the diffusing computation, outgoing deficit counter `deficit`, and
optional engagement-tree `parent`. -/
@[ext]
structure ProcState (P : Type*) where
  /-- Whether the process is currently active in the underlying diffusing computation. -/
  active : Bool
  /-- Outgoing basic messages sent minus acknowledgement signals received (`D` in `EWD687a`). -/
  deficit : ℕ
  /-- Incoming engagement-tree parent (`none` at `root` and when neutral/detached). -/
  parent : Option P
  deriving @[expose] DecidableEq, Repr

/-- An in-flight point-to-point basic message of the diffusing computation from `src` to `dst`. -/
@[ext]
structure BasicMsg (P : Type*) where
  /-- Sender process, whose `deficit` was incremented on transmission. -/
  src : P
  /-- Recipient process. -/
  dst : P
  deriving @[expose] DecidableEq, Repr

/-- Global configuration of an asynchronous diffusing computation with the Dijkstra–Scholten
control overlay. -/
@[ext]
structure State (P : Type*) where
  /-- Per-process local state (`active`, `deficit`, `parent`). -/
  proc : P → ProcState P
  /-- Unordered multiset of in-flight basic messages. -/
  basicMsgs : Multiset (BasicMsg P)
  /-- Unordered multiset of in-flight acknowledgement signals, represented by recipient `P`. -/
  signals : Multiset P

/-- Computable equality check on global states over a finite process type `P`. -/
instance instDecidableEqState {P : Type*} [Fintype P] [DecidableEq P] : DecidableEq (State P) :=
  fun s₁ s₂ =>
    decidable_of_iff
      ((∀ p, s₁.proc p = s₂.proc p) ∧ s₁.basicMsgs = s₂.basicMsgs ∧ s₁.signals = s₂.signals)
      ⟨fun ⟨hp, hb, hs⟩ => State.ext (funext hp) hb hs,
        fun h => h ▸ ⟨fun _ => rfl, rfl, rfl⟩⟩

/-- Initial configuration of a diffusing computation rooted at `root`: only `root` is `active`,
all deficits are `0`, all `parent` pointers are `none`, and all channels are empty. -/
@[expose]
def initState {P : Type*} [DecidableEq P] (root : P) : State P where
  proc p := { active := decide (p = root), deficit := 0, parent := none }
  basicMsgs := 0
  signals := 0

@[simp]
theorem initState_active {P : Type*} [DecidableEq P] (root p : P) :
    ((initState root).proc p).active = decide (p = root) := rfl

@[simp]
theorem initState_deficit {P : Type*} [DecidableEq P] (root p : P) :
    ((initState root).proc p).deficit = 0 := rfl

@[simp]
theorem initState_parent {P : Type*} [DecidableEq P] (root p : P) :
    ((initState root).proc p).parent = none := rfl

@[simp]
theorem initState_basicMsgs {P : Type*} [DecidableEq P] (root : P) :
    (initState root).basicMsgs = 0 := rfl

@[simp]
theorem initState_signals {P : Type*} [DecidableEq P] (root : P) :
    (initState root).signals = 0 := rfl

/-- Transition labels of the asynchronous Dijkstra–Scholten overlay. -/
inductive Action (P : Type*) where
  /-- Active `src` sends a basic message to `dst`, incrementing `deficit src`. -/
  | sendBasic (src dst : P)
  /-- Recipient `dst` receives in-flight basic message `⟨src, dst⟩`. -/
  | recvBasic (src dst : P)
  /-- Active process `p` becomes idle. -/
  | becomeIdle (p : P)
  /-- Process `p` receives an in-flight signal and decrements `deficit p`. -/
  | recvSignal (p : P)
  /-- Idle non-root `p` with `deficit p = 0` and `parent p = some q` detaches and signals `q`. -/
  | detach (p q : P)
  deriving @[expose] DecidableEq, Repr

namespace State

variable {P : Type*}

/-- Post-state of `Action.sendBasic src dst`. -/
@[expose]
def sendBasicState [DecidableEq P] (s : State P) (src dst : P) : State P where
  proc := Function.update s.proc src { s.proc src with deficit := (s.proc src).deficit + 1 }
  basicMsgs := ⟨src, dst⟩ ::ₘ s.basicMsgs
  signals := s.signals

/-- Post-state of `Action.recvBasic src dst` for diffusing root `root`.
If `dst ≠ root` and `(s.proc dst).parent = none` (which in every reachable state implies `dst` is
idle with `deficit = 0`), `dst` attaches with `parent := some src`; otherwise (`dst = root` or
`dst` is already engaged in the tree), `dst` keeps its `parent` and emits a signal to `src`. -/
@[expose]
def recvBasicState [DecidableEq P] (s : State P) (root src dst : P) : State P :=
  if dst ≠ root ∧ (s.proc dst).parent = none then
    { proc := Function.update s.proc dst { s.proc dst with active := true, parent := some src }
      basicMsgs := s.basicMsgs.erase ⟨src, dst⟩
      signals := s.signals }
  else
    { proc := Function.update s.proc dst { s.proc dst with active := true }
      basicMsgs := s.basicMsgs.erase ⟨src, dst⟩
      signals := src ::ₘ s.signals }

/-- Post-state of `Action.becomeIdle p`. -/
@[expose]
def becomeIdleState [DecidableEq P] (s : State P) (p : P) : State P where
  proc := Function.update s.proc p { s.proc p with active := false }
  basicMsgs := s.basicMsgs
  signals := s.signals

/-- Post-state of `Action.recvSignal p`. -/
@[expose]
def recvSignalState [DecidableEq P] (s : State P) (p : P) : State P where
  proc := Function.update s.proc p { s.proc p with deficit := (s.proc p).deficit - 1 }
  basicMsgs := s.basicMsgs
  signals := s.signals.erase p

/-- Post-state of `Action.detach p q`. -/
@[expose]
def detachState [DecidableEq P] (s : State P) (p q : P) : State P where
  proc := Function.update s.proc p { s.proc p with parent := none }
  basicMsgs := s.basicMsgs
  signals := q ::ₘ s.signals

/-- Root local termination condition (`EWD687a - 2`–`5`, PDF pp. 5–8): `root` is idle and its
deficit has returned to `0`. -/
@[expose]
def Terminated (s : State P) (root : P) : Prop :=
  (s.proc root).active = false ∧ (s.proc root).deficit = 0

instance instDecidableTerminated (s : State P) (root : P) : Decidable (s.Terminated root) :=
  inferInstanceAs (Decidable ((s.proc root).active = false ∧ (s.proc root).deficit = 0))

/-- Global quiescence of the network and control overlay: every process is idle with zero deficit
and `parent = none`, and both basic-message and signal channels are empty. -/
@[expose]
def GlobalQuiescent (s : State P) : Prop :=
  (∀ p : P, (s.proc p).active = false ∧ (s.proc p).deficit = 0 ∧ (s.proc p).parent = none) ∧
    s.basicMsgs = 0 ∧ s.signals = 0

instance instDecidableGlobalQuiescent [Fintype P] [DecidableEq P] (s : State P) :
    Decidable s.GlobalQuiescent :=
  inferInstanceAs (Decidable
    ((∀ p : P, (s.proc p).active = false ∧ (s.proc p).deficit = 0 ∧ (s.proc p).parent = none) ∧
      s.basicMsgs = 0 ∧ s.signals = 0))

theorem GlobalQuiescent.terminated {s : State P} (hq : s.GlobalQuiescent) (root : P) :
    s.Terminated root :=
  ⟨(hq.1 root).1, (hq.1 root).2.1⟩

/-- The underlying diffusing computation has ceased: all processes are idle and no basic messages
are in flight, though acknowledgement signals and tree detachments may still be draining. -/
@[expose]
def ComputationIdle (s : State P) : Prop :=
  (∀ p : P, (s.proc p).active = false) ∧ s.basicMsgs = 0

instance instDecidableComputationIdle [Fintype P] [DecidableEq P] (s : State P) :
    Decidable s.ComputationIdle :=
  inferInstanceAs (Decidable ((∀ p : P, (s.proc p).active = false) ∧ s.basicMsgs = 0))

theorem GlobalQuiescent.computationIdle {s : State P} (hq : s.GlobalQuiescent) :
    s.ComputationIdle :=
  ⟨fun p => (hq.1 p).1, hq.2.1⟩

end State

/-- Executable single-step transition evaluator for the Dijkstra–Scholten overlay rooted at
`root`. Returns `some s'` iff action `a` is enabled in `s` with post-state `s'`. -/
@[expose]
def step? {P : Type*} [DecidableEq P] (root : P) (s : State P) : Action P → Option (State P)
  | .sendBasic src dst =>
    if (s.proc src).active = true then some (s.sendBasicState src dst) else none
  | .recvBasic src dst =>
    if ⟨src, dst⟩ ∈ s.basicMsgs then some (s.recvBasicState root src dst) else none
  | .becomeIdle p =>
    if (s.proc p).active = true then some (s.becomeIdleState p) else none
  | .recvSignal p =>
    if p ∈ s.signals then some (s.recvSignalState p) else none
  | .detach p q =>
    if p ≠ root ∧ (s.proc p).active = false ∧ (s.proc p).deficit = 0 ∧
        (s.proc p).parent = some q then
      some (s.detachState p q)
    else
      none

/-- Execute a finite action trace `tr` from `s` under `step? root`. -/
@[expose]
def runTrace? {P : Type*} [DecidableEq P] (root : P) (s : State P) (tr : List (Action P)) :
    Option (State P) :=
  tr.foldlM (step? root) s

/-- Labelled transition system for the asynchronous Dijkstra–Scholten overlay rooted at `root`. -/
@[expose]
def lts {P : Type*} [DecidableEq P] (root : P) : LTS (State P) (Action P) where
  Tr s a s' := step? root s a = some s'

/-- Computable transition check for `(lts root).Tr s a s'` over a finite process type `P`. -/
instance instDecidableTr {P : Type*} [Fintype P] [DecidableEq P] (root : P) (s : State P)
    (a : Action P) (s' : State P) : Decidable ((lts root).Tr s a s') :=
  inferInstanceAs (Decidable (step? root s a = some s'))

/-- A global configuration `s` is reachable in the Dijkstra–Scholten overlay rooted at `root` if
`lts root` can reach `s` from `initState root`. -/
@[expose]
def Reachable {P : Type*} [DecidableEq P] (root : P) (s : State P) : Prop :=
  (lts root).CanReach (initState root) s

theorem Reachable.init {P : Type*} [DecidableEq P] (root : P) :
    Reachable root (initState root) :=
  LTS.CanReach.refl (lts root) (initState root)

theorem Reachable.step {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {a : Action P}
    (hr : Reachable root s) (htr : (lts root).Tr s a s') : Reachable root s' := by
  obtain ⟨tr, hmtr⟩ := hr
  exact ⟨tr ++ [a], hmtr.stepR (lts root) htr⟩

theorem Reachable.mtr {P : Type*} [DecidableEq P] {root : P} {s s' : State P}
    {tr : List (Action P)} (hr : Reachable root s) (hmtr : (lts root).MTr s tr s') :
    Reachable root s' := by
  obtain ⟨tr₀, hmtr₀⟩ := hr
  exact ⟨tr₀ ++ tr, hmtr₀.comp (lts root) hmtr⟩

/-- Every label at every state has at most one successor in `lts root`. -/
instance deterministic_lts {P : Type*} [DecidableEq P] (root : P) : (lts root).Deterministic where
  deterministic _ _ _ _ h₁ h₂ := Option.some.inj (h₁.symm.trans h₂)

@[simp]
theorem tr_sendBasic_iff {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {src dst : P} :
    (lts root).Tr s (.sendBasic src dst) s' ↔
      (s.proc src).active = true ∧ s.sendBasicState src dst = s' := by
  simp [lts, step?]

@[simp]
theorem tr_recvBasic_iff {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {src dst : P} :
    (lts root).Tr s (.recvBasic src dst) s' ↔
      ⟨src, dst⟩ ∈ s.basicMsgs ∧ s.recvBasicState root src dst = s' := by
  simp [lts, step?]

@[simp]
theorem tr_becomeIdle_iff {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {p : P} :
    (lts root).Tr s (.becomeIdle p) s' ↔
      (s.proc p).active = true ∧ s.becomeIdleState p = s' := by
  simp [lts, step?]

@[simp]
theorem tr_recvSignal_iff {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {p : P} :
    (lts root).Tr s (.recvSignal p) s' ↔
      p ∈ s.signals ∧ s.recvSignalState p = s' := by
  simp [lts, step?]

@[simp]
theorem tr_detach_iff {P : Type*} [DecidableEq P] {root : P} {s s' : State P} {p q : P} :
    (lts root).Tr s (.detach p q) s' ↔
      (p ≠ root ∧ (s.proc p).active = false ∧ (s.proc p).deficit = 0 ∧
        (s.proc p).parent = some q) ∧ s.detachState p q = s' := by
  simp [lts, step?]

/-- Multi-step transitions in `lts root` coincide with executable `runTrace?` evaluation. -/
theorem mtr_iff_runTrace?_eq_some {P : Type*} [DecidableEq P] {root : P} {s s' : State P}
    {tr : List (Action P)} :
    (lts root).MTr s tr s' ↔ runTrace? root s tr = some s' := by
  induction tr generalizing s with
  | nil => simp [runTrace?, eq_comm]
  | cons a tr ih =>
    simp only [LTS.MTr.cons_iff, ih]
    simp only [runTrace?, lts, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff]

end Cslib.Distributed.DijkstraScholten
