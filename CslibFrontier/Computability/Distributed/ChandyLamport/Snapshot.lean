/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ChandyLamport.Basic

/-!
# Chandy–Lamport marker snapshot transformation and FIFO cut invariants

This module defines the Chandy–Lamport global-state recording transformation ([ChandyLamport1985],
§3.2, p. 70) on top of any asynchronous FIFO message-passing `System P S M`, without freezing or
blocking underlying application transitions.

Wire channels carry `WireMsg M` values—either an application message `.app m` or a control
`.marker`. Each process `p` maintains:

* its live application state `appState : S`,
* its write-once recorded local state `snapState : Option S` (`none` before recording, `some s_p`
  once recorded), and
* per-incoming-channel recorders `chanRec : P → ChannelRec M` (`recording buf` while `p` has
  recorded its local state and is still awaiting `.marker` on `(q, p)`; `done saved` once
  `.marker` arrives, or immediately for the triggering channel and any non-edge).

The protocol obeys the two Chandy–Lamport rules:

1. **Marker-sending rule:** When `p` transitions from `snapState = none` to `some appState`—either
   spontaneously via `SnapEvent.initiateSnapshot p` or upon receiving its first `.marker` at the
   head of an incoming channel `(src, p)` via `SnapEvent.recvMarker src p`—it atomically records
   `appState`, marks incoming channel `(src, p)` (if marker-triggered) and non-edges `.done []`,
   initializes all other incoming channels `(q, p)` to `.recording []`, and appends `.marker` to
   every outgoing channel `(p, r)` of `sys.graph`.
2. **Marker-receiving rule:** If `p` has already recorded (`snapState = some _`), receiving `.app m`
   on `(src, p)` appends `m` to `chanRec src` whenever `chanRec src = .recording buf` while running
   `sys`'s normal `recv` transition; receiving `.marker` on `(src, p)` transitions `chanRec src`
   from `.recording buf` to `.done buf`.

In this LTS presentation, `SnapEvent.recvMarker src dest` executes the marker-sending or
marker-receiving rule atomically upon consuming `.marker` from the head of `(src, dest)`, and
`SnapEvent.stutter` extends finite quiescent runs to infinite executions for liveness (whereas the
underlying `sys.lts` has no stuttering action, so `sys.lts.IsTerminal` expresses genuine deadlock).

## Main definitions

* `Cslib.Distributed.ChandyLamport.WireMsg`, `Cslib.Distributed.ChandyLamport.unmarker`,
  `Cslib.Distributed.ChandyLamport.takeBeforeMarker`,
  `Cslib.Distributed.ChandyLamport.dropAfterMarker`: wire messages and FIFO channel projections
  before/after a `.marker`.
* `Cslib.Distributed.ChandyLamport.ChannelRec`: incoming-channel recorder (`recording` or `done`).
* `Cslib.Distributed.ChandyLamport.SnapProcState`,
  `Cslib.Distributed.ChandyLamport.SnapGlobalState`: snapshot-augmented local and global states.
* `Cslib.Distributed.ChandyLamport.project`, `Cslib.Distributed.ChandyLamport.liftState`,
  `Cslib.Distributed.ChandyLamport.extractSnapshot`: forgetful projection, pre-snapshot embedding,
  and assembled global snapshot `S*`.
* `Cslib.Distributed.ChandyLamport.SnapEvent`, `Cslib.Distributed.ChandyLamport.eraseTrace`:
  augmented transition labels and marker-step erasure.
* `Cslib.Distributed.ChandyLamport.System.snapLts`,
  `Cslib.Distributed.ChandyLamport.System.runSnapEvents`,
  `Cslib.Distributed.ChandyLamport.System.snapStates`,
  `Cslib.Distributed.ChandyLamport.System.validSnapTrace`: LTS of the Chandy–Lamport augmented
  system and its executable trace runners.
* `Cslib.Distributed.ChandyLamport.System.WellFormedSnapChan`,
  `Cslib.Distributed.ChandyLamport.System.IsPreSnapshot`,
  `Cslib.Distributed.ChandyLamport.IsSnapshotComplete`: channel well-formedness, pre-snapshot
  initial condition, and snapshot-completion predicate.
* `Cslib.Distributed.ChandyLamport.System.SnapInv`: inductive single-marker and FIFO cut invariant.

## Main results

* `Cslib.Distributed.ChandyLamport.System.snapMTr_iff_validSnapTrace`,
  `Cslib.Distributed.ChandyLamport.System.mem_snapStates_iff_split`: finite executions of
  `sys.snapLts` match `validSnapTrace` + `runSnapEvents`, and `snapStates` enumerates their exact
  intermediate states.
* `Cslib.Distributed.ChandyLamport.System.snapMTr_project`: erasing marker-control steps maps any
  augmented finite execution to a valid `sys.lts` execution from `project S₁` to `project S₂`.
* `Cslib.Distributed.ChandyLamport.System.snapTr_appInternal_of_tr`,
  `Cslib.Distributed.ChandyLamport.System.snapMTr_appRecv_of_tr`: non-blocking forward simulation
  of underlying `internal` and `recv` transitions in `sys.snapLts`.
* `Cslib.Distributed.ChandyLamport.System.snapInv_mTr`: `SnapInv` holds across all executions from
  any `IsPreSnapshot` state.
* `Cslib.Distributed.ChandyLamport.System.count_marker_le_one`: at most one `.marker` is ever in
  flight on any channel `(u, v)`.
* `Cslib.Distributed.ChandyLamport.System.isSnapshotComplete_no_markers`: once `IsSnapshotComplete`
  holds, zero `.marker`s remain in flight anywhere in the network.

## References

* [K. M. Chandy, L. Lamport, *Distributed Snapshots: Determining Global States of Distributed
  Systems*][ChandyLamport1985]
-/

public section

namespace Cslib.Distributed.ChandyLamport

open Cslib

/-! ### Wire messages and channel marker projections -/

/-- Wire message on a FIFO channel of the Chandy–Lamport augmented network. -/
inductive WireMsg (M : Type*) where
  /-- Normal underlying application payload. -/
  | app (m : M)
  /-- Chandy–Lamport snapshot control marker. -/
  | marker
  deriving @[expose] DecidableEq

/-- Extract `some m` from `.app m` and `none` from `.marker`. -/
@[expose] def WireMsg.toApp {M : Type*} : WireMsg M → Option M
  | .app m => some m
  | .marker => none

/-- Boolean test checking whether a `WireMsg` is `.marker` (without needing `DecidableEq M`). -/
@[expose] def WireMsg.isMarker {M : Type*} : WireMsg M → Bool
  | .app _ => false
  | .marker => true

@[simp]
theorem WireMsg.isMarker_eq_true_iff {M : Type*} {w : WireMsg M} :
    w.isMarker = true ↔ w = .marker := by
  cases w <;> simp [isMarker]

/-- Erase all `.marker`s from a wire channel, preserving the FIFO order of application messages. -/
@[expose] def unmarker {M : Type*} (ws : List (WireMsg M)) : List M :=
  ws.filterMap WireMsg.toApp

@[simp]
theorem unmarker_nil {M : Type*} : unmarker ([] : List (WireMsg M)) = [] := rfl

@[simp]
theorem unmarker_cons_app {M : Type*} (m : M) (ws : List (WireMsg M)) :
    unmarker (.app m :: ws) = m :: unmarker ws := rfl

@[simp]
theorem unmarker_cons_marker {M : Type*} (ws : List (WireMsg M)) :
    unmarker (.marker :: ws) = unmarker ws := rfl

@[simp]
theorem unmarker_append {M : Type*} (ws₁ ws₂ : List (WireMsg M)) :
    unmarker (ws₁ ++ ws₂) = unmarker ws₁ ++ unmarker ws₂ :=
  List.filterMap_append

@[simp]
theorem unmarker_map_app {M : Type*} (ms : List M) :
    unmarker (ms.map WireMsg.app) = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [ih]

theorem marker_notMem_map_app {M : Type*} (ms : List M) :
    WireMsg.marker ∉ ms.map WireMsg.app := by
  simp

/-- Application messages preceding the first `.marker` in a wire channel. -/
@[expose] def takeBeforeMarker {M : Type*} : List (WireMsg M) → List M
  | [] => []
  | .app m :: ws => m :: takeBeforeMarker ws
  | .marker :: _ => []

/-- Application messages strictly following the first `.marker` in a wire channel. -/
@[expose] def dropAfterMarker {M : Type*} : List (WireMsg M) → List M
  | [] => []
  | .app _ :: ws => dropAfterMarker ws
  | .marker :: ws => unmarker ws

theorem unmarker_eq_takeBeforeMarker_append_dropAfterMarker {M : Type*}
    (ws : List (WireMsg M)) :
    unmarker ws = takeBeforeMarker ws ++ dropAfterMarker ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w with
    | app m => simp [takeBeforeMarker, dropAfterMarker, ih]
    | marker => rfl

theorem takeBeforeMarker_append_marker_of_notMem {M : Type*} {ws : List (WireMsg M)}
    (h : .marker ∉ ws) : takeBeforeMarker (ws ++ [.marker]) = unmarker ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w with
    | app m =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      simp [takeBeforeMarker, ih h]
    | marker => exact absurd List.mem_cons_self h

theorem dropAfterMarker_append_marker_of_notMem {M : Type*} {ws : List (WireMsg M)}
    (h : .marker ∉ ws) : dropAfterMarker (ws ++ [.marker]) = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases w with
    | app m =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h
    | marker => exact absurd List.mem_cons_self h

theorem takeBeforeMarker_append_app_of_mem {M : Type*} {ws : List (WireMsg M)}
    (h : .marker ∈ ws) (ms : List M) :
    takeBeforeMarker (ws ++ ms.map .app) = takeBeforeMarker ws := by
  induction ws with
  | nil => cases h
  | cons w ws ih =>
    cases w with
    | app m =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      simp [takeBeforeMarker, ih h]
    | marker => rfl

theorem dropAfterMarker_append_app_of_mem {M : Type*} {ws : List (WireMsg M)}
    (h : .marker ∈ ws) (ms : List M) :
    dropAfterMarker (ws ++ ms.map .app) = dropAfterMarker ws ++ ms := by
  induction ws with
  | nil => cases h
  | cons w ws ih =>
    cases w with
    | app m =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact ih h
    | marker => simp [dropAfterMarker]

/-! ### Snapshot-augmented local and global configurations -/

/-- Per-incoming-channel recorder state at a process that has recorded its local snapshot. -/
inductive ChannelRec (M : Type*) where
  /-- Actively buffering application messages arriving on this channel until `.marker` arrives. -/
  | recording (buf : List M)
  /-- Recording finalized with saved message sequence `saved`. -/
  | done (saved : List M)
  deriving @[expose] DecidableEq

/-- Recorded message buffer currently stored in a `ChannelRec`. -/
@[expose] def ChannelRec.msgs {M : Type*} : ChannelRec M → List M
  | .recording buf => buf
  | .done saved => saved

/-- Boolean test checking whether a `ChannelRec` has reached `.done`. -/
@[expose] def ChannelRec.isDone {M : Type*} : ChannelRec M → Bool
  | .recording _ => false
  | .done _ => true

/-- Record incoming application message `m` if still `.recording`, or leave unchanged if `.done`. -/
@[expose] def ChannelRec.recordApp {M : Type*} (m : M) : ChannelRec M → ChannelRec M
  | .recording buf => .recording (buf ++ [m])
  | .done saved => .done saved

/-- Augmented local state of a process in the Chandy–Lamport snapshot protocol. -/
@[ext]
structure SnapProcState (P S M : Type*) where
  /-- Current local state in the underlying application system. -/
  appState : S
  /-- Recorded local state (`none` before recording, `some s_p` once recorded). -/
  snapState : Option S
  /-- Per-incoming-channel recorder state (active once `snapState.isSome`). -/
  chanRec : P → ChannelRec M

instance instDecidableEqSnapProcState {P S M : Type*}
    [Fintype P] [DecidableEq S] [DecidableEq M] :
    DecidableEq (SnapProcState P S M) := fun s₁ s₂ =>
  decidable_of_iff
    (s₁.appState = s₂.appState ∧ s₁.snapState = s₂.snapState ∧ s₁.chanRec = s₂.chanRec)
    ⟨fun ⟨h₁, h₂, h₃⟩ => SnapProcState.ext h₁ h₂ h₃, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-- Global configuration of the Chandy–Lamport snapshot-augmented system. -/
@[ext]
structure SnapGlobalState (P S M : Type*) where
  /-- Augmented local state of each process. -/
  proc : P → SnapProcState P S M
  /-- Point-to-point FIFO wire channels carrying application messages and markers. -/
  chan : P → P → List (WireMsg M)

instance instDecidableEqSnapGlobalState {P S M : Type*}
    [Fintype P] [DecidableEq S] [DecidableEq M] :
    DecidableEq (SnapGlobalState P S M) := fun s₁ s₂ =>
  decidable_of_iff (s₁.proc = s₂.proc ∧ s₁.chan = s₂.chan)
    ⟨fun ⟨hp, hc⟩ => SnapGlobalState.ext hp hc, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Project an augmented global configuration to its underlying `GlobalState` by forgetting snapshot
fields and erasing `.marker`s from every channel. -/
@[expose] def project {P S M : Type*} (S_aug : SnapGlobalState P S M) : GlobalState P S M where
  proc p := (S_aug.proc p).appState
  chan u v := unmarker (S_aug.chan u v)

/-- Embed an underlying `GlobalState` as an initial pre-snapshot `SnapGlobalState` with
`snapState = none` everywhere and no markers in flight. -/
@[expose] def liftState {P S M : Type*} (s : GlobalState P S M) : SnapGlobalState P S M where
  proc p := ⟨s.proc p, none, fun _ => .recording []⟩
  chan u v := (s.chan u v).map .app

@[simp]
theorem project_liftState {P S M : Type*} (s : GlobalState P S M) :
    project (liftState s) = s := by
  apply GlobalState.ext
  · rfl
  · funext u v
    exact unmarker_map_app (s.chan u v)

/-- Assemble the recorded global snapshot `S*` from `S_aug`: each process takes its recorded
`snapState` (falling back to `appState` only if unrecorded) and each channel `(q, p)` takes the
saved message sequence `((S_aug.proc p).chanRec q).msgs`. -/
@[expose] def extractSnapshot {P S M : Type*}
    (S_aug : SnapGlobalState P S M) : GlobalState P S M where
  proc p := ((S_aug.proc p).snapState).getD (S_aug.proc p).appState
  chan q p := ((S_aug.proc p).chanRec q).msgs

/-- Global snapshot recording is complete when every process has recorded its local state and every
incoming-channel recorder has reached `.done`. -/
@[expose] def IsSnapshotComplete {P S M : Type*} (S_aug : SnapGlobalState P S M) : Prop :=
  (∀ p, ((S_aug.proc p).snapState).isSome = true) ∧
  (∀ q p, (((S_aug.proc p).chanRec q)).isDone = true)

instance instDecidableIsSnapshotComplete {P S M : Type*} [Fintype P]
    (S_aug : SnapGlobalState P S M) : Decidable (IsSnapshotComplete S_aug) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Augmented transition labels and Chandy–Lamport rules -/

/-- Transition label of the Chandy–Lamport snapshot-augmented system. -/
inductive SnapEvent (P S M : Type*) where
  /-- Normal underlying application event (`internal` or `recv` of `.app m`). -/
  | app (e : Event P S M)
  /-- Spontaneous snapshot initiation by process `p` (when `snapState = none`). -/
  | initiateSnapshot (p : P)
  /-- Delivery of `.marker` at the head of channel `(src, dest)`. -/
  | recvMarker (src dest : P)
  /-- Stuttering step leaving the augmented state unchanged (used to extend finite executions to
  infinite executions). -/
  | stutter
  deriving @[expose] DecidableEq

/-- Extract `some e` for an application transition `.app e`, and `none` for pure snapshot/stutter
transitions. -/
@[expose] def SnapEvent.toAppEvent {P S M : Type*} : SnapEvent P S M → Option (Event P S M)
  | .app e => some e
  | .initiateSnapshot _ => none
  | .recvMarker _ _ => none
  | .stutter => none

/-- Erase pure marker-control and stuttering steps from an augmented trace, retaining underlying
application events in order. -/
@[expose] def eraseTrace {P S M : Type*} (xl : List (SnapEvent P S M)) : List (Event P S M) :=
  xl.filterMap SnapEvent.toAppEvent

@[simp]
theorem eraseTrace_nil {P S M : Type*} : eraseTrace ([] : List (SnapEvent P S M)) = [] := rfl

@[simp]
theorem eraseTrace_append {P S M : Type*} (xl₁ xl₂ : List (SnapEvent P S M)) :
    eraseTrace (xl₁ ++ xl₂) = eraseTrace xl₁ ++ eraseTrace xl₂ :=
  List.filterMap_append

/-- Apply an application event `e` to an augmented state `S_aug`: updates `appState`, pops `.app m`
if receiving, appends outgoing `.app` messages, and appends `m` to `chanRec src` if `dest` has
already recorded its local state and `chanRec src` is still `.recording`. -/
@[expose] def SnapGlobalState.applyApp {P S M : Type*} [DecidableEq P]
    (S_aug : SnapGlobalState P S M) (e : Event P S M) : SnapGlobalState P S M :=
  match e with
  | .internal p st' sent =>
    { proc r :=
        if r = p then { S_aug.proc p with appState := st' } else S_aug.proc r
      chan u v :=
        if u = p then S_aug.chan u v ++ (outgoingTo sent v).map .app else S_aug.chan u v }
  | .recv src dest msg st' sent =>
    let cur := S_aug.proc dest
    let newChanRec : P → ChannelRec M :=
      if cur.snapState.isSome then
        fun q => if q = src then (cur.chanRec src).recordApp msg else cur.chanRec q
      else cur.chanRec
    let popped u v := if u = src ∧ v = dest then (S_aug.chan u v).tail else S_aug.chan u v
    { proc r :=
        if r = dest then ⟨st', cur.snapState, newChanRec⟩ else S_aug.proc r
      chan u v :=
        if u = dest then popped u v ++ (outgoingTo sent v).map .app else popped u v }

namespace System

variable {P S M : Type*} (sys : System P S M)

/-- Apply spontaneous snapshot initiation at process `p` (Chandy–Lamport marker-sending rule):
records `appState`, sets `chanRec q := .recording []` on incoming edges (and `.done []` on
non-edges), and appends `.marker` to every outgoing edge `(p, r)`. -/
@[expose] def applyInitiate [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) (p : P) : SnapGlobalState P S M where
  proc r :=
    if r = p then
      let cur := S_aug.proc p
      ⟨cur.appState, some cur.appState,
        fun q => if sys.graph.Adj q p then .recording [] else .done []⟩
    else S_aug.proc r
  chan u v :=
    if u = p ∧ sys.graph.Adj p v then S_aug.chan u v ++ [.marker] else S_aug.chan u v

/-- Apply `.marker` receipt on channel `(src, dest)` (marker-sending rule on first marker arrival;
marker-receiving rule if `dest` has already recorded). -/
@[expose] def applyRecvMarker [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) (src dest : P) : SnapGlobalState P S M :=
  let popped u v := if u = src ∧ v = dest then (S_aug.chan u v).tail else S_aug.chan u v
  let cur := S_aug.proc dest
  match cur.snapState with
  | none =>
    { proc r :=
        if r = dest then
          ⟨cur.appState, some cur.appState,
            fun q => if q = src ∨ ¬ sys.graph.Adj q dest then .done [] else .recording []⟩
        else S_aug.proc r
      chan u v :=
        if u = dest ∧ sys.graph.Adj dest v then popped u v ++ [.marker] else popped u v }
  | some s_d =>
    { proc r :=
        if r = dest then
          ⟨cur.appState, some s_d,
            fun q => if q = src then .done (cur.chanRec src).msgs else cur.chanRec q⟩
        else S_aug.proc r
      chan := popped }

/-- Whether augmented event `a` is enabled in `S_aug`. -/
@[expose] def EnabledSnap (S_aug : SnapGlobalState P S M) : SnapEvent P S M → Prop
  | .app (.internal p st' sent) =>
    sys.internal p (S_aug.proc p).appState st' sent ∧
    ∀ rm ∈ sent, sys.graph.Adj p rm.1
  | .app (.recv src dest msg st' sent) =>
    sys.graph.Adj src dest ∧
    (S_aug.chan src dest).head? = some (.app msg) ∧
    sys.recv src dest (S_aug.proc dest).appState msg st' sent ∧
    ∀ rm ∈ sent, sys.graph.Adj dest rm.1
  | .initiateSnapshot p =>
    (S_aug.proc p).snapState = none
  | .recvMarker src dest =>
    sys.graph.Adj src dest ∧
    (S_aug.chan src dest).head? = some .marker
  | .stutter => True

instance instDecidableEnabledSnap [DecidableEq M] [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (S_aug : SnapGlobalState P S M) (a : SnapEvent P S M) :
    Decidable (sys.EnabledSnap S_aug a) := by
  cases a with
  | app e => cases e <;> exact inferInstanceAs (Decidable (_ ∧ _))
  | initiateSnapshot p => exact inferInstanceAs (Decidable (_ = none))
  | recvMarker src dest => exact inferInstanceAs (Decidable (_ ∧ _))
  | stutter => exact isTrue trivial

/-- Next augmented state reached from `S_aug` under `a`. -/
@[expose] def stepSnap [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : SnapEvent P S M → SnapGlobalState P S M
  | .app e => S_aug.applyApp e
  | .initiateSnapshot p => sys.applyInitiate S_aug p
  | .recvMarker src dest => sys.applyRecvMarker S_aug src dest
  | .stutter => S_aug

/-- Labelled transition system of the Chandy–Lamport snapshot-augmented network. -/
@[expose] def snapLts [DecidableEq P] [DecidableRel sys.graph.Adj] :
    LTS (SnapGlobalState P S M) (SnapEvent P S M) where
  Tr S_aug a S_aug' := sys.EnabledSnap S_aug a ∧ S_aug' = sys.stepSnap S_aug a

/-- `sys.snapLts` is deterministic. -/
instance snapLts_deterministic [DecidableEq P] [DecidableRel sys.graph.Adj] :
    sys.snapLts.Deterministic where
  deterministic _ _ _ _ h₁ h₂ := h₁.2.trans h₂.2.symm

/-- Augmented state reached from `S_aug` by applying each event in `xl` sequentially. -/
@[expose] def runSnapEvents [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : List (SnapEvent P S M) → SnapGlobalState P S M
  | [] => S_aug
  | a :: xl => runSnapEvents (sys.stepSnap S_aug a) xl

/-- Sequence of augmented states `(S_0, S_1, ..., S_k)` visited when executing `xl` from `S_aug`
(including both endpoints `S_aug` and `sys.runSnapEvents S_aug xl`). -/
@[expose] def snapStates [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : List (SnapEvent P S M) → List (SnapGlobalState P S M)
  | [] => [S_aug]
  | a :: xl => S_aug :: snapStates (sys.stepSnap S_aug a) xl

/-- Executable trace-validity predicate checking that each augmented event in `xl` is enabled when
reached from `S_aug`. -/
@[expose] def validSnapTrace [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : List (SnapEvent P S M) → Prop
  | [] => True
  | a :: xl => sys.EnabledSnap S_aug a ∧ validSnapTrace (sys.stepSnap S_aug a) xl

instance instDecidableValidSnapTrace [DecidableEq P] [DecidableEq M]
    [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (S_aug : SnapGlobalState P S M) (xl : List (SnapEvent P S M)) :
    Decidable (sys.validSnapTrace S_aug xl) := by
  induction xl generalizing S_aug with
  | nil => exact isTrue trivial
  | cons a xl ih =>
    have := ih (sys.stepSnap S_aug a)
    exact inferInstanceAs (Decidable (_ ∧ _))

/-- Because `sys.snapLts` is deterministic, `sys.snapLts.MTr S₁ xl S₂` holds if and only if `xl` is
a valid augmented trace from `S₁` and `S₂ = sys.runSnapEvents S₁ xl`. -/
theorem snapMTr_iff_validSnapTrace [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {xl : List (SnapEvent P S M)} :
    sys.snapLts.MTr S₁ xl S₂ ↔ sys.validSnapTrace S₁ xl ∧ S₂ = sys.runSnapEvents S₁ xl := by
  induction xl generalizing S₁ with
  | nil =>
    constructor
    · rintro ⟨⟩
      exact ⟨trivial, rfl⟩
    · rintro ⟨_, rfl⟩
      exact .refl
  | cons a xl ih =>
    constructor
    · rintro (_ | ⟨⟨hen, rfl⟩, hrest⟩)
      obtain ⟨hv, hr⟩ := ih.mp hrest
      exact ⟨⟨hen, hv⟩, hr⟩
    · rintro ⟨⟨hen, hv⟩, rfl⟩
      exact .stepL ⟨hen, rfl⟩ (ih.mpr ⟨hv, rfl⟩)

instance instDecidableSnapMTr [Fintype P] [DecidableEq P] [DecidableEq S] [DecidableEq M]
    [DecidableRel sys.graph.Adj]
    [∀ p st st' sent, Decidable (sys.internal p st st' sent)]
    [∀ src dest st msg st' sent, Decidable (sys.recv src dest st msg st' sent)]
    (S₁ S₂ : SnapGlobalState P S M) (xl : List (SnapEvent P S M)) :
    Decidable (sys.snapLts.MTr S₁ xl S₂) :=
  decidable_of_iff (sys.validSnapTrace S₁ xl ∧ S₂ = sys.runSnapEvents S₁ xl)
    sys.snapMTr_iff_validSnapTrace.symm

/-- Along any valid execution `S_init →*[xl] S_final` of `sys.snapLts`, `sys.snapStates S_init xl`
is the exact set of intermediate augmented states `S_k` reached by splitting `xl = xl₁ ++ xl₂`. -/
theorem mem_snapStates_iff_split [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_final S_k : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hmtr : sys.snapLts.MTr S_init xl S_final) :
    S_k ∈ sys.snapStates S_init xl ↔
      ∃ xl₁ xl₂, xl = xl₁ ++ xl₂ ∧
        sys.snapLts.MTr S_init xl₁ S_k ∧ sys.snapLts.MTr S_k xl₂ S_final := by
  induction hmtr with
  | @refl S₀ =>
    simp only [snapStates, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨[], [], rfl, .refl, .refl⟩
    · rintro ⟨xl₁, xl₂, heq, hm₁, _⟩
      obtain rfl := (List.append_eq_nil_iff.mp heq.symm).1
      cases hm₁
      rfl
  | @stepL S₀ a S₁ rest S_end htr hrest ih =>
    rcases htr with ⟨hen, rfl⟩
    simp only [snapStates, List.mem_cons]
    constructor
    · rintro (rfl | hmem)
      · exact ⟨[], a :: rest, rfl, .refl, .stepL ⟨hen, rfl⟩ hrest⟩
      · obtain ⟨xl₁, xl₂, rfl, hm₁, hm₂⟩ := ih.mp hmem
        exact ⟨a :: xl₁, xl₂, rfl, .stepL ⟨hen, rfl⟩ hm₁, hm₂⟩
    · rintro ⟨_ | ⟨b, xl₁'⟩, xl₂, heq, hm₁, hm₂⟩
      · cases hm₁
        exact Or.inl rfl
      · obtain ⟨rfl, hrest_eq⟩ := List.cons.inj heq
        rcases hm₁ with _ | ⟨⟨-, rfl⟩, hm₁'⟩
        exact Or.inr (ih.mpr ⟨xl₁', xl₂, hrest_eq, hm₁', hm₂⟩)

/-! ### Projection to the underlying system & non-blocking simulation -/

private lemma unmarker_singleton_marker {M : Type*} :
    unmarker ([.marker] : List (WireMsg M)) = [] := rfl

theorem snapTr_project [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {a : SnapEvent P S M}
    (htr : sys.snapLts.Tr S₁ a S₂) :
    match a.toAppEvent with
    | some e => sys.lts.Tr (project S₁) e (project S₂)
    | none => project S₂ = project S₁ := by
  obtain ⟨hen, rfl⟩ := htr
  cases a with
  | app e =>
    cases e with
    | internal p st' sent =>
      refine ⟨hen, ?_⟩
      apply GlobalState.ext
      · funext r
        simp only [project, stepSnap, SnapGlobalState.applyApp, GlobalState.applyEvent,
          GlobalState.applyLocal]
        rcases eq_or_ne r p with rfl | hr <;> simp_all
      · funext u v
        simp only [project, stepSnap, SnapGlobalState.applyApp, GlobalState.applyEvent,
          GlobalState.applyLocal]
        rcases eq_or_ne u p with rfl | hu <;> simp_all
    | recv src dest msg st' sent =>
      obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hen.2.1
      have hproj_head : ((project S₁).chan src dest).head? = some msg := by
        simp [project, ht]
      refine ⟨⟨hen.1, hproj_head, hen.2.2.1, hen.2.2.2⟩, ?_⟩
      apply GlobalState.ext
      · funext r
        simp only [project, stepSnap, SnapGlobalState.applyApp, GlobalState.applyEvent,
          GlobalState.applyLocal, GlobalState.popChan]
        rcases eq_or_ne r dest with rfl | hr <;> simp_all
      · funext u v
        simp only [project, stepSnap, SnapGlobalState.applyApp, GlobalState.applyEvent,
          GlobalState.applyLocal, GlobalState.popChan]
        by_cases hp : u = src ∧ v = dest
        · rcases hp with ⟨rfl, rfl⟩
          simp only [and_self, ↓reduceIte, ht, List.tail_cons, unmarker_cons_app]
          rcases eq_or_ne u v with rfl | hu <;> simp_all
        · simp only [hp, ↓reduceIte]
          by_cases hu : u = dest <;> simp [hu]
  | initiateSnapshot p =>
    apply GlobalState.ext
    · funext r
      simp only [project, stepSnap, applyInitiate]
      rcases eq_or_ne r p with rfl | hr <;> simp_all
    · funext u v
      simp only [project, stepSnap, applyInitiate]
      by_cases h : u = p ∧ sys.graph.Adj p v <;> simp [h]
  | recvMarker src dest =>
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hen.2
    apply GlobalState.ext
    · funext r
      simp only [project, stepSnap, applyRecvMarker]
      cases hsnap : (S₁.proc dest).snapState <;>
        (simp only; rcases eq_or_ne r dest with rfl | hr <;> simp_all)
    · funext u v
      have hpop : (if u = src ∧ v = dest then unmarker (S₁.chan u v).tail
          else unmarker (S₁.chan u v)) = unmarker (S₁.chan u v) := by
        split_ifs with h₂
        · obtain ⟨rfl, rfl⟩ := h₂; simp [ht]
        · rfl
      simp only [project, stepSnap, applyRecvMarker]
      cases (S₁.proc dest).snapState <;>
        simp only [apply_ite unmarker, unmarker_append, unmarker_singleton_marker, List.append_nil,
          hpop, ite_self]
  | stutter => rfl

/-- Erasing marker-control and stuttering steps maps any valid finite execution of `sys.snapLts`
to a valid finite execution of the underlying `sys.lts` from `project S₁` to `project S₂`. -/
theorem snapMTr_project [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hmtr : sys.snapLts.MTr S₁ xl S₂) :
    sys.lts.MTr (project S₁) (eraseTrace xl) (project S₂) := by
  induction hmtr with
  | refl => exact LTS.MTr.refl
  | @stepL S_a a S_b rest S_c htr _ ih =>
    have hstep := sys.snapTr_project htr
    cases ha : a.toAppEvent <;> rw [ha] at hstep <;> simp only [eraseTrace, List.filterMap_cons, ha]
    · rwa [← hstep]
    · exact LTS.MTr.stepL hstep ih

/-- Every spontaneous `internal` step enabled in `project S_aug` is immediately enabled as a single
`SnapEvent.app` step in `sys.snapLts` without blocking. -/
theorem snapTr_appInternal_of_tr [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) {p : P} {st' : S} {sent : List (P × M)}
    {s' : GlobalState P S M}
    (htr : sys.lts.Tr (project S_aug) (.internal p st' sent) s') :
    sys.snapLts.Tr S_aug (.app (.internal p st' sent))
      (S_aug.applyApp (.internal p st' sent)) ∧
      project (S_aug.applyApp (.internal p st' sent)) = s' := by
  obtain ⟨hen, rfl⟩ := htr
  have hsnap : sys.snapLts.Tr S_aug (.app (.internal p st' sent))
      (S_aug.applyApp (.internal p st' sent)) := ⟨hen, rfl⟩
  have hproj := sys.snapTr_project hsnap
  simp only [SnapEvent.toAppEvent] at hproj
  exact ⟨hsnap, hproj.2⟩

/-! ### Pre-snapshot condition and single-marker FIFO cut invariant -/

/-- An augmented state has well-formed channels if every non-edge of `sys.graph` is empty. -/
@[expose] def WellFormedSnapChan (S_aug : SnapGlobalState P S M) : Prop :=
  ∀ u v, ¬ sys.graph.Adj u v → S_aug.chan u v = []

instance instDecidableWellFormedSnapChan [Fintype P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : Decidable (sys.WellFormedSnapChan S_aug) :=
  inferInstanceAs (Decidable (∀ _ _, _))

private theorem wellFormedSnapChan_tr [DecidableEq P] [DecidableRel sys.graph.Adj] :
    sys.snapLts.TrInv sys.WellFormedSnapChan := by
  rintro S₁ a _ ⟨hen, rfl⟩ hwf u v huv
  cases a with
  | stutter => exact hwf u v huv
  | initiateSnapshot p =>
    have hnd : ¬ (u = p ∧ sys.graph.Adj p v) := by rintro ⟨rfl, ha⟩; exact huv ha
    simp [stepSnap, applyInitiate, hnd, hwf u v huv]
  | recvMarker src dest =>
    have hnp : ¬ (u = src ∧ v = dest) := by rintro ⟨rfl, rfl⟩; exact huv hen.1
    have hnd : ¬ (u = dest ∧ sys.graph.Adj dest v) := by rintro ⟨rfl, ha⟩; exact huv ha
    simp only [stepSnap, applyRecvMarker]
    cases (S₁.proc dest).snapState <;> simp [hnp, hnd, hwf u v huv]
  | app e =>
    cases e with
    | internal p st' sent =>
      simp only [stepSnap, SnapGlobalState.applyApp]
      rcases eq_or_ne u p with rfl | hu
      · have hout : outgoingTo sent v = [] :=
          outgoingTo_eq_nil_of_forall_ne fun m hm => huv (hen.2 (v, m) hm)
        simp [hwf u v huv, hout]
      · simp [hu, hwf u v huv]
    | recv src dest msg st' sent =>
      have hnp : ¬ (u = src ∧ v = dest) := by rintro ⟨rfl, rfl⟩; exact huv hen.1
      simp only [stepSnap, SnapGlobalState.applyApp, hnp, ↓reduceIte]
      rcases eq_or_ne u dest with rfl | hu
      · have hout : outgoingTo sent v = [] :=
          outgoingTo_eq_nil_of_forall_ne fun m hm => huv (hen.2.2.2 (v, m) hm)
        simp [hwf u v huv, hout]
      · simp [hu, hwf u v huv]

/-- Non-edge wire channels remain empty across any finite execution of `sys.snapLts`. -/
theorem wellFormedSnapChan_mTr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hmtr : sys.snapLts.MTr S₁ xl S₂) (hwf : sys.WellFormedSnapChan S₁) :
    sys.WellFormedSnapChan S₂ :=
  LTS.mtrInv_of_trInv sys.wellFormedSnapChan_tr S₁ xl S₂ hmtr hwf

/-- Pre-snapshot initial condition: no process has recorded yet (`snapState = none`), no `.marker`s
are in flight, and non-edge channels are empty (`WellFormedSnapChan`). -/
@[expose] def IsPreSnapshot (S_aug : SnapGlobalState P S M) : Prop :=
  (∀ p, (S_aug.proc p).snapState = none) ∧
  (∀ u v, .marker ∉ S_aug.chan u v) ∧
  sys.WellFormedSnapChan S_aug

instance instDecidableIsPreSnapshot [Fintype P] [DecidableEq M]
    [DecidableRel sys.graph.Adj] (S_aug : SnapGlobalState P S M) :
    Decidable (sys.IsPreSnapshot S_aug) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `liftState s` satisfies `IsPreSnapshot` whenever `s` has well-formed channels. -/
theorem isPreSnapshot_liftState {s : GlobalState P S M} (hwf : sys.WellFormedChan s) :
    sys.IsPreSnapshot (liftState s) :=
  ⟨fun _ => rfl,
   fun u v => marker_notMem_map_app (s.chan u v),
   fun u v huv => by simp [liftState, hwf u v huv]⟩

private lemma countP_isMarker_eq_zero_iff {M : Type*} {ws : List (WireMsg M)} :
    ws.countP WireMsg.isMarker = 0 ↔ .marker ∉ ws := by
  rw [List.countP_eq_zero]
  constructor
  · intro h hm
    exact absurd rfl (WireMsg.isMarker_eq_true_iff.not.mp (h .marker hm))
  · intro h w hw hmk
    exact h (WireMsg.isMarker_eq_true_iff.mp hmk ▸ hw)

private lemma countP_isMarker_append_app {M : Type*} (ws : List (WireMsg M)) (ms : List M) :
    (ws ++ ms.map WireMsg.app).countP WireMsg.isMarker = ws.countP WireMsg.isMarker := by
  rw [List.countP_append, countP_isMarker_eq_zero_iff.mpr (marker_notMem_map_app ms), add_zero]

private lemma notMem_tail_of_head_marker_of_countP_le_one {M : Type*} {ws : List (WireMsg M)}
    (hhead : ws.head? = some .marker) (hcnt : ws.countP WireMsg.isMarker ≤ 1) :
    .marker ∉ ws.tail := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hhead
  simp only [List.countP_cons, WireMsg.isMarker, ↓reduceIte, List.tail_cons] at hcnt ⊢
  exact countP_isMarker_eq_zero_iff.mp (by omega)

/-- Inductive invariant of the Chandy–Lamport snapshot protocol:
1. Non-edges carry empty channels and (once `v` records) `.done []` recorders.
2. Every channel holds at most one `.marker`.
3. While `u` has not recorded (`snapState = none`), `chan u v` contains no `.marker`, and if `v`
   has already recorded along edge `(u, v)`, `chanRec u` at `v` is `.recording buf`.
4. Once `u` has recorded along edge `(u, v)`, either `.marker ∈ chan u v` (and if `v` has recorded,
   `chanRec u` at `v` is `.recording buf`), or `.marker ∉ chan u v` (meaning `.marker` was already
   delivered to `v`, so `v` has recorded and `chanRec u` at `v` is `.done saved`). -/
structure SnapInv (S_aug : SnapGlobalState P S M) : Prop where
  /-- Non-edge channels stay empty and their recorders are `.done []`. -/
  nonEdge : ∀ u v, ¬ sys.graph.Adj u v →
    S_aug.chan u v = [] ∧
    ((S_aug.proc v).snapState.isSome = true → (S_aug.proc v).chanRec u = .done [])
  /-- At most one `.marker` is ever in flight on `(u, v)`. -/
  markerCount : ∀ u v, (S_aug.chan u v).countP WireMsg.isMarker ≤ 1
  /-- Unrecorded senders have emitted no `.marker`, and recorded receivers on `(u, v)` are still
  recording from `u`. -/
  unrecordedSrc : ∀ u v, (S_aug.proc u).snapState = none →
    .marker ∉ S_aug.chan u v ∧
    ((S_aug.proc v).snapState.isSome = true → sys.graph.Adj u v →
      ∃ buf, (S_aug.proc v).chanRec u = .recording buf)
  /-- Recorded senders on `(u, v)` either still have `.marker` in flight (with `v` recording if
  recorded) or have already had `.marker` delivered (with `v` recorded and `chanRec u = .done`). -/
  recordedSrc : ∀ u v, (S_aug.proc u).snapState.isSome = true → sys.graph.Adj u v →
    (.marker ∈ S_aug.chan u v ∧
      ((S_aug.proc v).snapState.isSome = true →
        ∃ buf, (S_aug.proc v).chanRec u = .recording buf)) ∨
    (.marker ∉ S_aug.chan u v ∧
      (S_aug.proc v).snapState.isSome = true ∧
      ∃ saved, (S_aug.proc v).chanRec u = .done saved)

theorem snapInv_of_isPreSnapshot {S_aug : SnapGlobalState P S M}
    (hpre : sys.IsPreSnapshot S_aug) : sys.SnapInv S_aug where
  nonEdge u v huv := ⟨hpre.2.2 u v huv, by rw [hpre.1 v]; simp⟩
  markerCount u v := by
    rw [countP_isMarker_eq_zero_iff.mpr (hpre.2.1 u v)]
    exact Nat.zero_le 1
  unrecordedSrc u v _ := ⟨hpre.2.1 u v, by rw [hpre.1 v]; simp⟩
  recordedSrc u _ hu := by rw [hpre.1 u] at hu; simp at hu

theorem enabledSnap_recvMarker_spec {S₁ : SnapGlobalState P S M} {src dest : P}
    (hinv : sys.SnapInv S₁) (hen : sys.EnabledSnap S₁ (.recvMarker src dest)) :
    sys.graph.Adj src dest ∧
    (S₁.proc src).snapState.isSome = true ∧
    ∃ t_sd, S₁.chan src dest = .marker :: t_sd ∧ .marker ∉ t_sd := by
  obtain ⟨hadj_sd, hhead_sd⟩ := hen
  obtain ⟨t_sd, ht_sd⟩ := List.head?_eq_some_iff.mp hhead_sd
  have hmem_sd : .marker ∈ S₁.chan src dest := by simp [ht_sd]
  have hsrc_some : (S₁.proc src).snapState.isSome = true := by
    cases h : (S₁.proc src).snapState with
    | none => exact absurd hmem_sd (hinv.unrecordedSrc src dest h).1
    | some _ => rfl
  have hnotm_tail : .marker ∉ t_sd := by
    simpa [ht_sd] using
      notMem_tail_of_head_marker_of_countP_le_one hhead_sd (hinv.markerCount src dest)
  exact ⟨hadj_sd, hsrc_some, t_sd, ht_sd, hnotm_tail⟩

private lemma recording_of_eq_or_recordApp {M : Type*} {r r' : ChannelRec M} {buf : List M}
    (h : r' = r ∨ ∃ m, r' = r.recordApp m) (hr : r = .recording buf) :
    ∃ buf', r' = .recording buf' := by
  subst hr; rcases h with rfl | ⟨m, rfl⟩ <;> exact ⟨_, rfl⟩

private lemma eq_done_of_eq_or_recordApp {M : Type*} {r r' : ChannelRec M} {sv : List M}
    (h : r' = r ∨ ∃ m, r' = r.recordApp m) (hr : r = .done sv) : r' = .done sv := by
  subst hr; rcases h with rfl | ⟨m, rfl⟩ <;> rfl

private theorem SnapInv.of_snapState_eq {sys : System P S M} {S₁ S₂ : SnapGlobalState P S M}
    (hinv : sys.SnapInv S₁) (hwf₂ : sys.WellFormedSnapChan S₂)
    (hsnap : ∀ v, (S₂.proc v).snapState = (S₁.proc v).snapState)
    (hcnt₂ : ∀ u v, (S₂.chan u v).countP WireMsg.isMarker ≤ 1)
    (hpair : ∀ u v,
      ((.marker ∈ S₂.chan u v ↔ .marker ∈ S₁.chan u v) ∧
        ((S₁.proc v).snapState.isSome = true →
          (S₂.proc v).chanRec u = (S₁.proc v).chanRec u ∨
          ∃ m, (S₂.proc v).chanRec u = ((S₁.proc v).chanRec u).recordApp m)) ∨
      (sys.graph.Adj u v ∧ (S₁.proc u).snapState.isSome = true ∧
        (S₁.proc v).snapState.isSome = true ∧ .marker ∉ S₂.chan u v ∧
        ∃ sv, (S₂.proc v).chanRec u = .done sv)) :
    sys.SnapInv S₂ where
  nonEdge u v huv := ⟨hwf₂ u v huv, fun hv₂ => by
    rw [hsnap v] at hv₂
    rcases hpair u v with ⟨_, hcr⟩ | ⟨hadj, _⟩
    · exact eq_done_of_eq_or_recordApp (hcr hv₂) ((hinv.nonEdge u v huv).2 hv₂)
    · exact absurd hadj huv⟩
  markerCount := hcnt₂
  unrecordedSrc u v hu₂ := by
    rw [hsnap u] at hu₂
    obtain ⟨hnotm₁, hrec₁⟩ := hinv.unrecordedSrc u v hu₂
    rcases hpair u v with ⟨hm_iff, hcr⟩ | ⟨_, hu_some, _⟩
    · refine ⟨mt hm_iff.mp hnotm₁, fun hv₂ hadj => ?_⟩
      rw [hsnap v] at hv₂
      obtain ⟨buf, hbuf⟩ := hrec₁ hv₂ hadj
      exact recording_of_eq_or_recordApp (hcr hv₂) hbuf
    · rw [hu₂] at hu_some; nomatch hu_some
  recordedSrc u v hu₂ hadj := by
    rw [hsnap u] at hu₂
    rcases hpair u v with ⟨hm_iff, hcr⟩ | ⟨_, _, hv₁, hnotm₂, hsv₂⟩
    · rcases hinv.recordedSrc u v hu₂ hadj with ⟨hmem₁, hrec₁⟩ | ⟨hnotm₁, hv₁, ⟨sv, hsv⟩⟩
      · refine Or.inl ⟨hm_iff.mpr hmem₁, fun hv₂ => ?_⟩
        rw [hsnap v] at hv₂
        obtain ⟨buf, hbuf⟩ := hrec₁ hv₂
        exact recording_of_eq_or_recordApp (hcr hv₂) hbuf
      · exact Or.inr ⟨mt hm_iff.mp hnotm₁, (hsnap v).symm ▸ hv₁, sv,
          eq_done_of_eq_or_recordApp (hcr hv₁) hsv⟩
    · exact Or.inr ⟨hnotm₂, (hsnap v).symm ▸ hv₁, hsv₂⟩

private theorem SnapInv.of_record_node {sys : System P S M} [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {d : P}
    (hinv : sys.SnapInv S₁) (hwf₂ : sys.WellFormedSnapChan S₂)
    (hd_none : (S₁.proc d).snapState = none)
    (hd_some : (S₂.proc d).snapState.isSome = true)
    (hproc_ne : ∀ v, v ≠ d → S₂.proc v = S₁.proc v)
    (hd_nonEdge : ∀ u, ¬ sys.graph.Adj u d → (S₂.proc d).chanRec u = .done [])
    (hd_self : sys.graph.Adj d d → (S₂.proc d).chanRec d = .recording [])
    (hchan_d : ∀ v,
      S₂.chan d v = if sys.graph.Adj d v then S₁.chan d v ++ [.marker] else S₁.chan d v)
    (hother : ∀ u v, u ≠ d →
      (S₂.chan u v = S₁.chan u v ∧
        (v = d → sys.graph.Adj u d → (S₂.proc d).chanRec u = .recording [])) ∨
      (v = d ∧ sys.graph.Adj u d ∧ (S₁.proc u).snapState.isSome = true ∧
        .marker ∉ S₂.chan u d ∧ (S₂.proc d).chanRec u = .done [])) :
    sys.SnapInv S₂ where
  nonEdge u v huv := ⟨hwf₂ u v huv, fun hv₂ => by
    rcases eq_or_ne v d with rfl | hvd
    · exact hd_nonEdge u huv
    · rw [hproc_ne v hvd] at hv₂ ⊢; exact (hinv.nonEdge u v huv).2 hv₂⟩
  markerCount u v := by
    rcases eq_or_ne u d with rfl | hud
    · rw [hchan_d v]
      split_ifs with hadj
      · have hnotm := (hinv.unrecordedSrc u v hd_none).1
        simp [List.countP_append, countP_isMarker_eq_zero_iff.mpr hnotm, WireMsg.isMarker]
      · exact hinv.markerCount u v
    · rcases hother u v hud with ⟨hch, _⟩ | ⟨rfl, _, _, hnotm₂, _⟩
      · rw [hch]; exact hinv.markerCount u v
      · rw [countP_isMarker_eq_zero_iff.mpr hnotm₂]; exact Nat.zero_le 1
  unrecordedSrc u v hu₂ := by
    have hud : u ≠ d := fun h => by subst h; rw [hu₂] at hd_some; nomatch hd_some
    rw [hproc_ne u hud] at hu₂
    obtain ⟨hnotm₁, hrec₁⟩ := hinv.unrecordedSrc u v hu₂
    rcases hother u v hud with ⟨hch, hd_rec⟩ | ⟨_, _, hu_some, _⟩
    · refine ⟨hch ▸ hnotm₁, fun hv₂ hadj => ?_⟩
      rcases eq_or_ne v d with rfl | hvd
      · exact ⟨[], hd_rec rfl hadj⟩
      · rw [hproc_ne v hvd] at hv₂ ⊢; exact hrec₁ hv₂ hadj
    · rw [hu₂] at hu_some; nomatch hu_some
  recordedSrc u v hu₂ hadj := by
    rcases eq_or_ne u d with rfl | hud
    · refine Or.inl ⟨by rw [hchan_d v, ite_eq_left hadj]; simp, fun hv₂ => ?_⟩
      rcases eq_or_ne v u with rfl | hvd
      · exact ⟨[], hd_self hadj⟩
      · rw [hproc_ne v hvd] at hv₂ ⊢; exact (hinv.unrecordedSrc u v hd_none).2 hv₂ hadj
    · rw [hproc_ne u hud] at hu₂
      rcases hother u v hud with ⟨hch, hd_rec⟩ | ⟨rfl, _, _, hnotm₂, hdone₂⟩
      · rcases hinv.recordedSrc u v hu₂ hadj with ⟨hmem₁, hrec₁⟩ | ⟨hnotm₁, hv₁, hdone₁⟩
        · refine Or.inl ⟨hch ▸ hmem₁, fun hv₂ => ?_⟩
          rcases eq_or_ne v d with rfl | hvd
          · exact ⟨[], hd_rec rfl hadj⟩
          · rw [hproc_ne v hvd] at hv₂ ⊢; exact hrec₁ hv₂
        · have hvd : v ≠ d := fun h => by subst h; rw [hd_none] at hv₁; nomatch hv₁
          rw [hch, hproc_ne v hvd]
          exact Or.inr ⟨hnotm₁, hv₁, hdone₁⟩
      · exact Or.inr ⟨hnotm₂, hd_some, ⟨[], hdone₂⟩⟩

/-- `SnapInv` is preserved by every single transition of `sys.snapLts`. -/
theorem snapInv_tr [DecidableEq P] [DecidableRel sys.graph.Adj] :
    sys.snapLts.TrInv sys.SnapInv := by
  rintro S₁ a _ ⟨hen, rfl⟩ hinv
  have hwf₂ : sys.WellFormedSnapChan (sys.stepSnap S₁ a) :=
    sys.wellFormedSnapChan_tr S₁ a (sys.stepSnap S₁ a) ⟨hen, rfl⟩
      (fun u v huv => (hinv.nonEdge u v huv).1)
  cases a with
  | stutter => exact hinv
  | app e =>
    have hsnap_app : ∀ v, ((S₁.applyApp e).proc v).snapState = (S₁.proc v).snapState := fun v => by
      cases e <;> (simp only [SnapGlobalState.applyApp]; split_ifs with h <;> simp [h])
    cases e with
    | internal p st' sent =>
      refine hinv.of_snapState_eq hwf₂ hsnap_app
        (fun u v => by
          simp only [stepSnap, SnapGlobalState.applyApp]
          split_ifs <;> simp only [countP_isMarker_append_app, hinv.markerCount])
        fun u v => Or.inl ⟨by
          simp only [stepSnap, SnapGlobalState.applyApp]
          split_ifs <;> simp [marker_notMem_map_app],
          fun _ => Or.inl (by
            simp only [stepSnap, SnapGlobalState.applyApp]; split_ifs with h <;> simp [h])⟩
    | recv src dest msg st' sent =>
      obtain ⟨t_pop, ht_pop⟩ := List.head?_eq_some_iff.mp hen.2.1
      have hpop_mem : ∀ u v,
          .marker ∈ (if u = src ∧ v = dest then (S₁.chan u v).tail else S₁.chan u v) ↔
            .marker ∈ S₁.chan u v := fun u v => by
        by_cases hp : u = src ∧ v = dest
        · rcases hp with ⟨rfl, rfl⟩; simp [ht_pop]
        · simp [hp]
      refine hinv.of_snapState_eq hwf₂ hsnap_app
        (fun u v => by
          have hcnt_pop :
              (if u = src ∧ v = dest then (S₁.chan u v).tail else S₁.chan u v).countP
                WireMsg.isMarker ≤ 1 := by
            split_ifs
            exacts [(List.tail_sublist _).countP_le.trans (hinv.markerCount u v),
              hinv.markerCount u v]
          simp only [stepSnap, SnapGlobalState.applyApp]
          rcases eq_or_ne u dest with rfl | hu
          · simpa only [↓reduceIte, countP_isMarker_append_app] using hcnt_pop
          · simpa only [hu, ↓reduceIte] using hcnt_pop)
        fun u v => Or.inl ⟨by
          simp only [stepSnap, SnapGlobalState.applyApp]
          rcases eq_or_ne u dest with rfl | hu
          · simp [hpop_mem, marker_notMem_map_app]
          · simp [hu, hpop_mem],
          fun hv_some => by
            simp only [stepSnap, SnapGlobalState.applyApp]
            rcases eq_or_ne v dest with rfl | hv
            · simp only [↓reduceIte, hv_some]
              rcases eq_or_ne u src with rfl | husrc
              · exact Or.inr ⟨msg, by simp⟩
              · exact Or.inl (by simp [husrc])
            · exact Or.inl (by simp [hv])⟩
  | initiateSnapshot p =>
    exact hinv.of_record_node hwf₂ hen (by simp [stepSnap, applyInitiate])
      (fun v hv => by simp [stepSnap, applyInitiate, hv])
      (fun u huv => by simp [stepSnap, applyInitiate, huv])
      (fun hadj => by simp [stepSnap, applyInitiate, hadj])
      (fun v => by simp [stepSnap, applyInitiate])
      fun u v hu => Or.inl ⟨by simp [stepSnap, applyInitiate, hu],
        fun hv hadj => by subst hv; simp [stepSnap, applyInitiate, hadj]⟩
  | recvMarker src dest =>
    obtain ⟨hadj_sd, hsrc_some, t_sd, ht_sd, hnotm_tail_list⟩ :=
      sys.enabledSnap_recvMarker_spec hinv hen
    have hnotm_tail : .marker ∉ (S₁.chan src dest).tail := by simpa [ht_sd] using hnotm_tail_list
    cases hdest : (S₁.proc dest).snapState with
    | none =>
      simp only [stepSnap, applyRecvMarker, hdest] at hwf₂ ⊢
      have hsrc_ne_dest : src ≠ dest := fun h => by
        subst h; rw [hdest] at hsrc_some; nomatch hsrc_some
      exact hinv.of_record_node hwf₂ hdest (by simp)
        (fun v hv => by simp [hv])
        (fun u huv => by simp [huv])
        (fun hadj => by simp [hsrc_ne_dest.symm, hadj])
        (fun v => by simp [show ¬ (dest = src ∧ v = dest) from fun hp => hsrc_ne_dest hp.1.symm])
        fun u v hu => by
          by_cases hsd : u = src ∧ v = dest
          · rcases hsd with ⟨rfl, rfl⟩
            exact Or.inr ⟨rfl, hadj_sd, hsrc_some, by simp [hu, hnotm_tail], by simp⟩
          · exact Or.inl ⟨by simp [hu, hsd], fun hv hadj => by
              subst hv; simp [show u ≠ src from fun h => hsd ⟨h, rfl⟩, hadj]⟩
    | some s_d =>
      simp only [stepSnap, applyRecvMarker, hdest] at hwf₂ ⊢
      refine hinv.of_snapState_eq hwf₂
        (fun v => by by_cases hv : v = dest <;> simp [hv, hdest])
        (fun u v => by
          by_cases hsd : u = src ∧ v = dest
          · rcases hsd with ⟨rfl, rfl⟩
            simp [countP_isMarker_eq_zero_iff.mpr hnotm_tail]
          · simpa only [hsd, ↓reduceIte] using hinv.markerCount u v)
        fun u v => by
          by_cases hsd : u = src ∧ v = dest
          · rcases hsd with ⟨rfl, rfl⟩
            exact Or.inr ⟨hadj_sd, hsrc_some, by simp [hdest],
              by simp [hnotm_tail],
              ⟨((S₁.proc v).chanRec u).msgs, by simp⟩⟩
          · refine Or.inl ⟨by simp [hsd], fun _ => Or.inl ?_⟩
            rcases eq_or_ne v dest with rfl | hv
            · simp [show u ≠ src from fun h => hsd ⟨h, rfl⟩]
            · simp [hv]

/-- `SnapInv` holds at the end of every finite execution starting from an `IsPreSnapshot` state. -/
theorem snapInv_mTr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_aug : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hpre : sys.IsPreSnapshot S_init) (hmtr : sys.snapLts.MTr S_init xl S_aug) :
    sys.SnapInv S_aug :=
  LTS.mtrInv_of_trInv sys.snapInv_tr S_init xl S_aug hmtr (sys.snapInv_of_isPreSnapshot hpre)

/-- **Single-marker bound:** along any execution from a pre-snapshot state, every channel holds at
most one `.marker`. -/
theorem count_marker_le_one [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_aug : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hpre : sys.IsPreSnapshot S_init) (hmtr : sys.snapLts.MTr S_init xl S_aug) (u v : P) :
    (S_aug.chan u v).countP WireMsg.isMarker ≤ 1 :=
  (sys.snapInv_mTr hpre hmtr).markerCount u v

/-- **No markers remain upon completion:** once every process has recorded (`snapState.isSome`) and
every channel recorder has reached `.done`, zero `.marker`s remain in flight on any channel. -/
theorem isSnapshotComplete_no_markers {S_aug : SnapGlobalState P S M}
    (hinv : sys.SnapInv S_aug) (hcomp : IsSnapshotComplete S_aug) (u v : P) :
    .marker ∉ S_aug.chan u v := by
  by_cases hadj : sys.graph.Adj u v
  · rcases hinv.recordedSrc u v (hcomp.1 u) hadj with ⟨_, hrec⟩ | ⟨hnotm, _, _⟩
    · obtain ⟨buf, hbuf⟩ := hrec (hcomp.1 v)
      have hdone := hcomp.2 u v
      rw [hbuf] at hdone
      simp [ChannelRec.isDone] at hdone
    · exact hnotm
  · rw [(hinv.nonEdge u v hadj).1]
    simp

/-- Under `SnapInv S_aug`, any underlying `recv` transition enabled in `project S_aug` can execute
in `sys.snapLts` in at most two steps (optionally delivering a single leading `.marker` on
`(src, dest)` first, then delivering `.app msg`) without waiting on any other channel or process. -/
theorem snapMTr_appRecv_of_tr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_aug : SnapGlobalState P S M} (hinv : sys.SnapInv S_aug)
    {src dest : P} {msg : M} {st' : S} {sent : List (P × M)} {s' : GlobalState P S M}
    (htr : sys.lts.Tr (project S_aug) (.recv src dest msg st' sent) s') :
    ∃ xl S_aug',
      xl.length ≤ 2 ∧
      eraseTrace xl = [.recv src dest msg st' sent] ∧
      sys.snapLts.MTr S_aug xl S_aug' ∧
      project S_aug' = s' := by
  obtain ⟨⟨hadj, hhead, hrecv, hsent⟩, rfl⟩ := htr
  simp only [project] at hhead hrecv
  cases hch : S_aug.chan src dest with
  | nil =>
    rw [hch] at hhead
    simp at hhead
  | cons w ws =>
    cases w with
    | app m' =>
      rw [hch, unmarker_cons_app, List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      let e := Event.recv src dest m' st' sent
      have htr_app : sys.snapLts.Tr S_aug (.app e) (S_aug.applyApp e) :=
        ⟨⟨hadj, by simp [hch], hrecv, hsent⟩, rfl⟩
      have hproj := sys.snapTr_project htr_app
      simp only [SnapEvent.toAppEvent] at hproj
      exact ⟨[.app e], S_aug.applyApp e, by simp, rfl,
        LTS.MTr.single sys.snapLts htr_app, hproj.2⟩
    | marker =>
      have hnotm_ws : .marker ∉ ws := by
        simpa [hch] using notMem_tail_of_head_marker_of_countP_le_one
          (ws := S_aug.chan src dest) (by simp [hch]) (hinv.markerCount src dest)
      rw [hch, unmarker_cons_marker] at hhead
      rcases ws with _ | ⟨m' | _, ws₂⟩
      · simp at hhead
      · simp only [unmarker_cons_app, List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        let S₁ := sys.applyRecvMarker S_aug src dest
        have htr_mk : sys.snapLts.Tr S_aug (.recvMarker src dest) S₁ :=
          ⟨⟨hadj, by simp [hch]⟩, rfl⟩
        have hS₁_head : (S₁.chan src dest).head? = some (.app m') := by
          dsimp only [S₁, applyRecvMarker]
          cases (S_aug.proc dest).snapState
          · simp only [and_self, ↓reduceIte, hch, List.tail_cons]
            by_cases hd : src = dest ∧ sys.graph.Adj dest dest <;> simp [hd]
          · simp [hch]
        have hS₁_app : (S₁.proc dest).appState = (S_aug.proc dest).appState := by
          simp only [S₁, applyRecvMarker]
          cases (S_aug.proc dest).snapState <;> simp
        let e := Event.recv src dest m' st' sent
        have htr_app : sys.snapLts.Tr S₁ (.app e) (S₁.applyApp e) :=
          ⟨⟨hadj, hS₁_head, hS₁_app ▸ hrecv, hsent⟩, rfl⟩
        have hmtr : sys.snapLts.MTr S_aug [.recvMarker src dest, .app e] (S₁.applyApp e) :=
          LTS.MTr.stepL htr_mk (LTS.MTr.single sys.snapLts htr_app)
        have hproj := sys.snapMTr_project hmtr
        simp only [eraseTrace, List.filterMap_cons, SnapEvent.toAppEvent, List.filterMap_nil,
          LTS.MTr.singleton_iff] at hproj
        exact ⟨[.recvMarker src dest, .app e], S₁.applyApp e, by simp, rfl, hmtr, hproj.2⟩
      · exact absurd List.mem_cons_self hnotm_ws

end System

end Cslib.Distributed.ChandyLamport
