/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-!
# Rotational Symmetry Steps on Anonymous Rings

Synchronous-round and sequential-FIFO-wave rotational symmetry steps on anonymous oriented rings
`Fin n` (steps towards [Angluin][Angluin1980b], not the general processor-network covering
impossibility endpoints of `[Angluin1980b]`).

Every processor in an anonymous ring starts in the same initial state `init` without a distinct
identifier and executes the same deterministic transition function. Because a protocol value may
be chosen separately for each ring size `n`, these symmetry steps hold even when `n` is common
knowledge among the processors. Both bidirectional and unidirectional message passing are covered
in two concrete ring models:

1. **Synchronous rounds (`AnonProtocol`):** in round `r`, each node `i : Fin n` sends `toPred r s`
   counter-clockwise to `i - 1` and `toSucc r s` clockwise to `i + 1`, then updates via
   `recv r s fromPred fromSucc`. Shifting the initial state assignment by `+ k` commutes with
   every round (`AnonProtocol.stateFrom_shift_eq`), so from a uniform initial state all nodes
   share the exact same state after every round (`AnonProtocol.state_shift_eq`). Consequently, for
   `2 ≤ n` the set of self-declared leaders has cardinality `0` or `n`, never `1`
   (`AnonProtocol.not_electsUniqueLeader_sync_of_two_le`).
2. **Asynchronous FIFO schedules (`AnonAsyncProtocol`):** directed edges `i → i + 1` and
   `i → i - 1` carry unbounded FIFO queues modelled as a `Cslib.LTS`. Finite delivery schedules
   commute with cyclic index shifts (`AnonAsyncProtocol.exec_shift_eq`). Moreover, sequential
   round-robin FIFO waves delivering one message along every clockwise or counter-clockwise edge
   (`clockwiseWave`, `counterWave`) are valid `LTS.MTr` executions whenever the corresponding
   queues are nonempty and preserve exact rotational symmetry across all nodes
   (`AnonAsyncProtocol.exists_rotWave_trace_leaders_card_ne_one`).

## Main definitions

* `Cslib.Distributed.RingElection.AnonProtocol`, `AnonProtocol.unidir`: synchronous bidirectional
  (and unidirectional) anonymous ring protocols, with `stateFrom`, `run`, `leaders`, and
  `ElectsUniqueLeader`.
* `Cslib.Distributed.RingElection.RingDir`, `AnonAsyncOut`, `AnonAsyncProtocol`,
  `AnonAsyncProtocol.unidir`: asynchronous FIFO bidirectional (and unidirectional) anonymous ring
  protocols.
* `Cslib.Distributed.RingElection.AnonAsyncConfig`, `AnonEvent`, `AnonAsyncProtocol.lts`: global
  FIFO configurations, delivery events, and the labelled transition system of enabled deliveries.
* `Cslib.Distributed.RingElection.clockwiseWave`, `counterWave`, `rotSchedule`: sequential
  single-delivery FIFO waves preserving rotational invariance.

## Main results

* `Cslib.Distributed.RingElection.AnonProtocol.stateFrom_shift_eq`,
  `Cslib.Distributed.RingElection.AnonProtocol.state_shift_eq`: rotational equivariance and
  invariance of synchronous rounds on `Fin n`.
* `Cslib.Distributed.RingElection.AnonProtocol.leaders_card_eq_zero_or_self`: in any round, either
  `0` or all `n` nodes declare leadership.
* `Cslib.Distributed.RingElection.AnonProtocol.not_electsUniqueLeader_sync_of_two_le`:
  synchronous-round symmetry step on `Fin n` (`2 ≤ n`, after `[Angluin1980b]`).
* `Cslib.Distributed.RingElection.AnonAsyncProtocol.exec_shift_eq`: cyclic shift equivariance of
  asynchronous FIFO schedules.
* `Cslib.Distributed.RingElection.AnonAsyncProtocol.mtr_rotWave_uniform`,
  `Cslib.Distributed.RingElection.AnonAsyncProtocol.exists_rotWave_trace_leaders_card_ne_one`:
  sequential FIFO wave uniformity and rotational-wave symmetry step on `Fin n` (`2 ≤ n`, after
  `[Angluin1980b]`).

## References

* [D. Angluin, *Local and Global Properties in Networks of Processors*][Angluin1980b]
-/

public section

namespace Cslib.Distributed.RingElection

open Cslib

/-! ### Synchronous anonymous ring protocols -/

/-- A deterministic synchronous message-passing protocol for an anonymous oriented ring.

Every node starts in the common initial state `init`. In round `r`, each node `i` sends
`toPred r s` counter-clockwise to `i - 1` and `toSucc r s` clockwise to `i + 1`, then updates its
state via `recv r s fromPred fromSucc` where `fromPred` arrived from `i - 1` and `fromSucc`
arrived from `i + 1`. Because an `AnonProtocol` may depend on the ring size `n`, impossibility
applies even when `n` is known to all nodes. -/
structure AnonProtocol (S M : Type*) where
  /-- Common initial local state shared by all nodes before round `0`. -/
  init : S
  /-- Message sent counter-clockwise to predecessor `i - 1` in round `r`. -/
  toPred : ℕ → S → M
  /-- Message sent clockwise to successor `i + 1` in round `r`. -/
  toSucc : ℕ → S → M
  /-- Next state after round `r` from own state, message from `i - 1`, and message from `i + 1`. -/
  recv : ℕ → S → M → M → S
  /-- Boolean output predicate indicating whether a node declares itself leader. -/
  isLeader : S → Bool

namespace AnonProtocol

variable {S M : Type*} (P : AnonProtocol S M)

/-- Embed a unidirectional clockwise anonymous protocol (where each node sends `send r s` only to
`i + 1` and updates solely from its own state and the message received from `i - 1`) as an
`AnonProtocol`. The counter-clockwise field `toPred` is ignored by `recv`. -/
@[expose] def unidir (init : S) (send : ℕ → S → M) (recv : ℕ → S → M → S) (isLeader : S → Bool) :
    AnonProtocol S M where
  init := init
  toPred := send
  toSucc := send
  recv r s fromPred _ := recv r s fromPred
  isLeader := isLeader

/-- State of node `i : Fin n` after `r` synchronous rounds from an arbitrary initial state
assignment `s₀ : Fin n → S`. -/
@[expose] def stateFrom {n : ℕ} [NeZero n] (s₀ : Fin n → S) : ℕ → Fin n → S
  | 0, i => s₀ i
  | r + 1, i =>
    P.recv r (stateFrom s₀ r i)
      (P.toSucc r (stateFrom s₀ r (i - 1)))
      (P.toPred r (stateFrom s₀ r (i + 1)))

/-- State of node `i : Fin n` after `r` synchronous rounds from the anonymous uniform initial
configuration `fun _ => P.init`. -/
@[expose] def run (n : ℕ) [NeZero n] (r : ℕ) (i : Fin n) : S :=
  P.stateFrom (fun _ => P.init) r i

@[simp] theorem stateFrom_zero {n : ℕ} [NeZero n] (s₀ : Fin n → S) (i : Fin n) :
    P.stateFrom s₀ 0 i = s₀ i := rfl

private theorem stateFrom_succ {n : ℕ} [NeZero n] (s₀ : Fin n → S) (r : ℕ) (i : Fin n) :
    P.stateFrom s₀ (r + 1) i =
      P.recv r (P.stateFrom s₀ r i)
        (P.toSucc r (P.stateFrom s₀ r (i - 1)))
        (P.toPred r (P.stateFrom s₀ r (i + 1))) := rfl

@[simp] theorem run_zero (n : ℕ) [NeZero n] (i : Fin n) : P.run n 0 i = P.init := rfl

/-- Shifting node indices by `+ k` mod `n` commutes with every synchronous round on `Fin n`. -/
theorem stateFrom_shift_eq {n : ℕ} [NeZero n] (s₀ : Fin n → S) (k : Fin n) (r : ℕ) (i : Fin n) :
    P.stateFrom s₀ r (i + k) = P.stateFrom (fun j => s₀ (j + k)) r i := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih => rw [stateFrom_succ, stateFrom_succ, add_sub_right_comm, add_right_comm, ih, ih, ih]

/-- From a uniform initial state on `Fin n`, shifting any node index by `+ k` mod `n` leaves its
state unchanged after every synchronous round `r`. -/
theorem state_shift_eq (n : ℕ) [NeZero n] (r : ℕ) (i k : Fin n) :
    P.run n r (i + k) = P.run n r i :=
  P.stateFrom_shift_eq (fun _ => P.init) k r i

private theorem run_eq (n : ℕ) [NeZero n] (r : ℕ) (i j : Fin n) :
    P.run n r i = P.run n r j :=
  add_sub_cancel j i ▸ P.state_shift_eq n r j (i - j)

private theorem isLeader_run_forall_of_exists (n : ℕ) [NeZero n] (r : ℕ)
    (hex : ∃ i : Fin n, P.isLeader (P.run n r i) = true) :
    ∀ i : Fin n, P.isLeader (P.run n r i) = true :=
  let ⟨i₀, hi₀⟩ := hex
  fun i => P.run_eq n r i i₀ ▸ hi₀

/-- The set of nodes declaring `isLeader = true` after `r` rounds on `Fin n`. -/
@[expose] def leaders (n : ℕ) [NeZero n] (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => P.isLeader (P.run n r i) = true

/-- Unique leader election at round `r`: exactly one node in `Fin n` declares `isLeader = true`. -/
@[expose] def ElectsUniqueLeader (n : ℕ) [NeZero n] (r : ℕ) : Prop :=
  (P.leaders n r).card = 1

/-- `ElectsUniqueLeader` is equivalent to unique existence
`∃! i, P.isLeader (P.run n r i) = true`. -/
theorem electsUniqueLeader_iff_existsUnique (n : ℕ) [NeZero n] (r : ℕ) :
    P.ElectsUniqueLeader n r ↔ ∃! i : Fin n, P.isLeader (P.run n r i) = true := by
  rw [ElectsUniqueLeader, Finset.card_eq_one]
  simp only [Finset.eq_singleton_iff_unique_mem, leaders, Finset.mem_filter, Finset.mem_univ,
    true_and, ExistsUnique]

/-- After any round `r`, the number of leaders in an anonymous `n`-ring is either `0` or `n`. -/
theorem leaders_card_eq_zero_or_self (n : ℕ) [NeZero n] (r : ℕ) :
    (P.leaders n r).card = 0 ∨ (P.leaders n r).card = n := by
  by_cases hex : ∃ i : Fin n, P.isLeader (P.run n r i) = true
  · refine Or.inr (Eq.trans (congrArg Finset.card (Finset.eq_univ_iff_forall.mpr fun i => ?_))
      (Fintype.card_fin n))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, P.isLeader_run_forall_of_exists n r hex i⟩
  · exact Or.inl (Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun i hi =>
      hex ⟨i, (Finset.mem_filter.mp hi).2⟩))

/-- A synchronous-round symmetry step on anonymous oriented rings `Fin n` (a step towards
[Angluin][Angluin1980b], not the general processor-network covering endpoint): for `2 ≤ n`, no
deterministic `AnonProtocol`—bidirectional or unidirectional, even parameterized by `n`—elects a
unique leader in any synchronous round `r`. -/
theorem not_electsUniqueLeader_sync_of_two_le {n : ℕ} [NeZero n] (hn : 2 ≤ n) (r : ℕ) :
    ¬ P.ElectsUniqueLeader n r := by
  rw [ElectsUniqueLeader]
  rcases P.leaders_card_eq_zero_or_self n r with h0 | hn_eq <;> omega

end AnonProtocol

/-! ### Asynchronous FIFO anonymous ring protocols -/

/-- Ring traversal direction for asynchronous FIFO channels: `clockwise` (`i - 1 → i`) or
`counter` (`i + 1 → i`). -/
inductive RingDir where
  /-- Delivery along clockwise edge `i - 1 → i`. -/
  | clockwise
  /-- Delivery along counter-clockwise edge `i + 1 → i`. -/
  | counter
  deriving @[expose] DecidableEq

/-- Output of a single asynchronous message reception: updated local state together with outgoing
FIFO messages appended to counter-clockwise (`toPred`) and clockwise (`toSucc`) channels. -/
structure AnonAsyncOut (S M : Type*) where
  /-- Updated local state of the receiving processor. -/
  nextState : S
  /-- Messages appended to the outgoing counter-clockwise channel `i → i - 1`. -/
  toPred : List M
  /-- Messages appended to the outgoing clockwise channel `i → i + 1`. -/
  toSucc : List M
  deriving @[expose] DecidableEq

/-- A deterministic asynchronous FIFO protocol for an anonymous bidirectional ring. -/
structure AnonAsyncProtocol (S M : Type*) where
  /-- Common initial local state of every node. -/
  init : S
  /-- Initial messages queued on every outgoing counter-clockwise channel `i → i - 1`. -/
  initToPred : List M
  /-- Initial messages queued on every outgoing clockwise channel `i → i + 1`. -/
  initToSucc : List M
  /-- Handler invoked when receiving the head of incoming clockwise channel `i - 1 → i`. -/
  recvFromPred : S → M → AnonAsyncOut S M
  /-- Handler invoked when receiving the head of incoming counter-clockwise channel `i + 1 → i`. -/
  recvFromSucc : S → M → AnonAsyncOut S M
  /-- Boolean predicate indicating whether a node declares itself leader. -/
  isLeader : S → Bool

/-- Global configuration of an asynchronous bidirectional FIFO ring on `Fin n`. -/
@[ext]
structure AnonAsyncConfig (n : ℕ) (S M : Type*) where
  /-- Local state of each node `i : Fin n`. -/
  node : Fin n → S
  /-- Clockwise FIFO queue on directed edge `i → i + 1` (head is oldest, tail is newest). -/
  chanSucc : Fin n → List M
  /-- Counter-clockwise FIFO queue on directed edge `i → i - 1` (head is oldest, tail is newest). -/
  chanPred : Fin n → List M

/-- A single-message delivery event in an asynchronous ring, delivering the head of the `dir`
channel incident to `target`. -/
structure AnonEvent (n : ℕ) where
  /-- Direction of the channel from which `target` receives. -/
  dir : RingDir
  /-- Receiving node `target : Fin n`. -/
  target : Fin n
  deriving @[expose] DecidableEq

/-- Cyclically shift an `AnonEvent` by `+ k` mod `n`. -/
@[expose] def AnonEvent.shift {n : ℕ} (k : Fin n) (e : AnonEvent n) : AnonEvent n :=
  ⟨e.dir, e.target + k⟩

/-- Cyclically shift an `AnonAsyncConfig` by `+ k` mod `n`. -/
@[expose] def AnonAsyncConfig.shift {n : ℕ} {S M : Type*} (k : Fin n)
    (cfg : AnonAsyncConfig n S M) : AnonAsyncConfig n S M where
  node i := cfg.node (i + k)
  chanSucc i := cfg.chanSucc (i + k)
  chanPred i := cfg.chanPred (i + k)

/-- Whether delivery event `e` is enabled in configuration `cfg` (its source FIFO queue is
nonempty). -/
@[expose] def AnonAsyncConfig.Enabled {n : ℕ} [NeZero n] {S M : Type*}
    (cfg : AnonAsyncConfig n S M) (e : AnonEvent n) : Prop :=
  match e.dir with
  | .clockwise => cfg.chanSucc (e.target - 1) ≠ []
  | .counter => cfg.chanPred (e.target + 1) ≠ []

/-- A configuration is uniform (rotationally symmetric) with state `s`, clockwise queue `cs`, and
counter-clockwise queue `cp` at every node. -/
@[expose] def AnonAsyncConfig.IsUniform {n : ℕ} {S M : Type*}
    (cfg : AnonAsyncConfig n S M) (s : S) (cs cp : List M) : Prop :=
  (∀ i, cfg.node i = s) ∧ (∀ i, cfg.chanSucc i = cs) ∧ (∀ i, cfg.chanPred i = cp)

/-- Sequential clockwise FIFO wave delivering one message to each node `0, 1, …, n - 1` in order. -/
@[expose] def clockwiseWave (n : ℕ) : List (AnonEvent n) :=
  (List.finRange n).map (AnonEvent.mk .clockwise)

/-- Sequential counter-clockwise FIFO wave delivering one message to each node
`0, -1, -2, …` in order (the `i ↦ -i` reflection of `clockwiseWave`). -/
@[expose] def counterWave (n : ℕ) : List (AnonEvent n) :=
  (List.finRange n).map fun i => ⟨.counter, -i⟩

/-- Concatenation of sequential single-delivery FIFO waves for a list of directions. -/
@[expose] def rotSchedule (n : ℕ) (dirs : List RingDir) : List (AnonEvent n) :=
  dirs.flatMap fun d =>
    match d with
    | .clockwise => clockwiseWave n
    | .counter => counterWave n

namespace AnonAsyncProtocol

variable {S M : Type*} (P : AnonAsyncProtocol S M)

/-- Construct a unidirectional clockwise asynchronous FIFO protocol where messages travel only
along `i → i + 1` (each reception from `i - 1` produces `nextState` and outgoing messages
`sendSucc`). -/
@[expose] def unidir (init : S) (initMsgs : List M) (nextState : S → M → S)
    (sendSucc : S → M → List M) (isLeader : S → Bool) : AnonAsyncProtocol S M where
  init := init
  initToPred := []
  initToSucc := initMsgs
  recvFromPred s m := ⟨nextState s m, [], sendSucc s m⟩
  recvFromSucc s _ := ⟨s, [], []⟩
  isLeader := isLeader

/-- Initial uniform configuration of `P` on `Fin n`. -/
@[expose] def initConfig (n : ℕ) : AnonAsyncConfig n S M where
  node _ := P.init
  chanSucc _ := P.initToSucc
  chanPred _ := P.initToPred

/-- Deterministic single-event FIFO transition (no-op if the addressed incoming queue is empty). -/
@[expose] def step {n : ℕ} [NeZero n] (e : AnonEvent n) (cfg : AnonAsyncConfig n S M) :
    AnonAsyncConfig n S M :=
  match e.dir with
  | .clockwise =>
    match cfg.chanSucc (e.target - 1) with
    | [] => cfg
    | m :: rest =>
      let out := P.recvFromPred (cfg.node e.target) m
      let succ₁ := Function.update cfg.chanSucc (e.target - 1) rest
      { node := Function.update cfg.node e.target out.nextState
        chanSucc := Function.update succ₁ e.target (succ₁ e.target ++ out.toSucc)
        chanPred := Function.update cfg.chanPred e.target (cfg.chanPred e.target ++ out.toPred) }
  | .counter =>
    match cfg.chanPred (e.target + 1) with
    | [] => cfg
    | m :: rest =>
      let out := P.recvFromSucc (cfg.node e.target) m
      let pred₁ := Function.update cfg.chanPred (e.target + 1) rest
      { node := Function.update cfg.node e.target out.nextState
        chanSucc := Function.update cfg.chanSucc e.target (cfg.chanSucc e.target ++ out.toSucc)
        chanPred := Function.update pred₁ e.target (pred₁ e.target ++ out.toPred) }

/-- Execute a finite asynchronous schedule `sched` starting from `cfg`. -/
@[expose] def exec {n : ℕ} [NeZero n] (cfg : AnonAsyncConfig n S M) (sched : List (AnonEvent n)) :
    AnonAsyncConfig n S M :=
  sched.foldl (fun c e => P.step e c) cfg

private theorem exec_cons {n : ℕ} [NeZero n] (cfg : AnonAsyncConfig n S M) (e : AnonEvent n)
    (es : List (AnonEvent n)) :
    P.exec cfg (e :: es) = P.exec (P.step e cfg) es := rfl

private theorem exec_map_eq_self {n : ℕ} [NeZero n] {α : Type*} {f : α → AnonEvent n}
    {c : AnonAsyncConfig n S M} (h : ∀ a, P.step (f a) c = c) (xs : List α) :
    P.exec c (xs.map f) = c := by
  induction xs with
  | nil => rfl
  | cons a as ih => rwa [List.map_cons, exec_cons, h]

/-- Labelled transition system of enabled single-message FIFO deliveries on `Fin n`. -/
@[expose] def lts (n : ℕ) [NeZero n] : LTS (AnonAsyncConfig n S M) (AnonEvent n) where
  Tr cfg e cfg' := cfg.Enabled e ∧ cfg' = P.step e cfg

/-- Set of nodes declaring `isLeader = true` in configuration `cfg`. -/
@[expose] def configLeaders {n : ℕ} (cfg : AnonAsyncConfig n S M) : Finset (Fin n) :=
  Finset.univ.filter fun i => P.isLeader (cfg.node i) = true

private theorem update_shift {n : ℕ} {α : Type*} (f : Fin n → α) (a k : Fin n) (v : α)
    (i : Fin n) :
    Function.update (fun j => f (j + k)) a v i = Function.update f (a + k) v (i + k) := by
  by_cases h : i = a
  · subst h
    simp only [Function.update_self]
  · have hk : i + k ≠ a + k := fun heq => h (add_right_cancel heq)
    simp only [Function.update_of_ne h, Function.update_of_ne hk]

private theorem step_shift_eq {n : ℕ} [NeZero n] (e : AnonEvent n) (k : Fin n)
    (cfg : AnonAsyncConfig n S M) :
    P.step e (cfg.shift k) = (P.step (e.shift k) cfg).shift k := by
  obtain ⟨dir, t⟩ := e
  cases dir
  · simp only [step, AnonEvent.shift, AnonAsyncConfig.shift]
    have hpred : t - 1 + k = t + k - 1 := (add_sub_right_comm t k 1).symm
    rw [hpred]
    cases hq : cfg.chanSucc (t + k - 1) with
    | nil => rfl
    | cons m rest =>
      refine AnonAsyncConfig.ext (funext (update_shift cfg.node t k _)) (funext fun i => ?_)
        (funext (update_shift cfg.chanPred t k _))
      dsimp only [AnonAsyncConfig.shift]
      have h1 : Function.update (fun j => cfg.chanSucc (j + k)) (t - 1) rest =
          fun j => Function.update cfg.chanSucc (t + k - 1) rest (j + k) :=
        funext fun j => hpred ▸ update_shift cfg.chanSucc (t - 1) k rest j
      rw [h1]
      exact update_shift (Function.update cfg.chanSucc (t + k - 1) rest) t k _ i
  · simp only [step, AnonEvent.shift, AnonAsyncConfig.shift]
    have hsucc : t + 1 + k = t + k + 1 := (add_right_comm t k 1).symm
    rw [hsucc]
    cases hq : cfg.chanPred (t + k + 1) with
    | nil => rfl
    | cons m rest =>
      refine AnonAsyncConfig.ext (funext (update_shift cfg.node t k _))
        (funext (update_shift cfg.chanSucc t k _)) (funext fun i => ?_)
      dsimp only [AnonAsyncConfig.shift]
      have h1 : Function.update (fun j => cfg.chanPred (j + k)) (t + 1) rest =
          fun j => Function.update cfg.chanPred (t + k + 1) rest (j + k) :=
        funext fun j => hsucc ▸ update_shift cfg.chanPred (t + 1) k rest j
      rw [h1]
      exact update_shift (Function.update cfg.chanPred (t + k + 1) rest) t k _ i

/-- Shifting node indices by `+ k` commutes with any finite asynchronous FIFO schedule on
`Fin n`. -/
theorem exec_shift_eq {n : ℕ} [NeZero n] (cfg : AnonAsyncConfig n S M) (k : Fin n)
    (sched : List (AnonEvent n)) :
    P.exec (cfg.shift k) sched = (P.exec cfg (sched.map (AnonEvent.shift k))).shift k := by
  induction sched generalizing cfg with
  | nil => rfl
  | cons e es ih =>
    simp only [exec_cons, List.map_cons]
    rw [P.step_shift_eq e k cfg, ih]

private theorem fin_sub_one_val {n : ℕ} [NeZero n] (i : Fin n) :
    (i - 1).val = if i.val = 0 then n - 1 else i.val - 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases eq_or_ne n 1 with rfl | hn1
  · have hi : i.val < 1 := i.isLt
    have hsub : (i - 1).val < 1 := (i - 1).isLt
    split_ifs <;> omega
  · have h1 : (1 : Fin n).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.sub_def, h1]
    change (n - 1 + i.val) % n = if i.val = 0 then n - 1 else i.val - 1
    split_ifs with hi
    · rw [hi, Nat.add_zero]
      exact Nat.mod_eq_of_lt (by omega)
    · have hq : n - 1 + i.val = n + (i.val - 1) := by omega
      rw [hq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- Partial state invariant after firing clockwise deliveries `0, 1, …, k - 1` on `Fin n` (`n ≥ 2`)
starting from a uniform configuration with clockwise queue `m :: ms`. -/
private def ClockWaveInv {n : ℕ} (s s' : S) (m : M) (ms newSucc cp newPred : List M)
    (k : ℕ) (cfg : AnonAsyncConfig n S M) : Prop :=
  (∀ i : Fin n, cfg.node i = if i.val < k then s' else s) ∧
  (∀ i : Fin n, cfg.chanPred i = if i.val < k then cp ++ newPred else cp) ∧
  (∀ i : Fin n, cfg.chanSucc i =
    if i.val < k - 1 then ms ++ newSucc
    else if i.val = k - 1 then m :: (ms ++ newSucc)
    else if i.val = n - 1 then ms
    else m :: ms)

private theorem clockWaveInv_at {n : ℕ} [NeZero n] {s s' : S} {m : M}
    {ms newSucc cp newPred : List M} {k : ℕ} (hk : 1 ≤ k)
    (c : AnonAsyncConfig n S M) (tk : Fin n) (htk_val : tk.val = k)
    (hInv : ClockWaveInv s s' m ms newSucc cp newPred k c) :
    (tk - 1).val = k - 1 ∧
      c.chanSucc (tk - 1) = m :: (ms ++ newSucc) ∧
      c.node tk = s ∧
      c.chanPred tk = cp ∧
      c.Enabled ⟨.clockwise, tk⟩ := by
  obtain ⟨hInode, hIpred, hIsucc⟩ := hInv
  have htk_pred_val : (tk - 1).val = k - 1 := by
    rw [fin_sub_one_val, htk_val]
    split_ifs <;> omega
  have hc_pred : c.chanSucc (tk - 1) = m :: (ms ++ newSucc) := by
    simpa [htk_pred_val] using hIsucc (tk - 1)
  refine ⟨htk_pred_val, hc_pred, by simpa [htk_val] using hInode tk,
    by simpa [htk_val] using hIpred tk, ?_⟩
  simp only [AnonAsyncConfig.Enabled, hc_pred, ne_eq, reduceCtorEq, not_false_iff]

private theorem step_clockwise_of_cons {n : ℕ} [NeZero n] {c : AnonAsyncConfig n S M}
    {t : Fin n} {m : M} {rest : List M} (hq : c.chanSucc (t - 1) = m :: rest) :
    let out := P.recvFromPred (c.node t) m
    (∀ i, (P.step ⟨.clockwise, t⟩ c).node i = if i = t then out.nextState else c.node i) ∧
    (∀ i, (P.step ⟨.clockwise, t⟩ c).chanPred i =
      if i = t then c.chanPred t ++ out.toPred else c.chanPred i) ∧
    (∀ i, (P.step ⟨.clockwise, t⟩ c).chanSucc i =
      (if i = t - 1 then rest else c.chanSucc i) ++ (if i = t then out.toSucc else [])) := by
  refine ⟨fun i => by simp only [step, hq, Function.update_apply],
    fun i => by simp only [step, hq, Function.update_apply], fun i => ?_⟩
  rcases eq_or_ne i t with rfl | hit
  · simp only [step, hq, Function.update_apply, ↓reduceIte]
  · simp only [step, hq, Function.update_apply, hit, ↓reduceIte, List.append_nil]

private theorem mtr_clockwiseWave_uniform {n : ℕ} [NeZero n] {cfg : AnonAsyncConfig n S M}
    {s : S} {m : M} {ms cp : List M} (huni : cfg.IsUniform s (m :: ms) cp) :
    (P.lts n).MTr cfg (clockwiseWave n) (P.exec cfg (clockwiseWave n)) ∧
      (P.exec cfg (clockwiseWave n)).IsUniform
        (P.recvFromPred s m).nextState
        (ms ++ (P.recvFromPred s m).toSucc)
        (cp ++ (P.recvFromPred s m).toPred) := by
  let out := P.recvFromPred s m
  obtain ⟨hnode, hsucc, hpred⟩ := huni
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn_pos) with hn1 | hn2
  · subst hn1
    have hfin1 : List.finRange 1 = [(0 : Fin 1)] := rfl
    have h0sub : (0 : Fin 1) - 1 = 0 := Subsingleton.elim _ _
    have hen : cfg.Enabled ⟨.clockwise, 0⟩ := by
      simp only [AnonAsyncConfig.Enabled, h0sub, hsucc 0, ne_eq, reduceCtorEq, not_false_iff]
    obtain ⟨hsn, hsp, hss⟩ := P.step_clockwise_of_cons (t := 0) (h0sub ▸ hsucc 0)
    simp only [clockwiseWave, hfin1, List.map, exec, List.foldl, AnonAsyncConfig.IsUniform]
    refine ⟨LTS.MTr.single (P.lts 1) ⟨hen, rfl⟩, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · rw [hsn i, ite_eq_left (Subsingleton.elim i 0), hnode 0]
    · rw [hss i, ite_eq_left (Subsingleton.elim i _), ite_eq_left (Subsingleton.elim i 0), hnode 0]
    · rw [hsp i, ite_eq_left (Subsingleton.elim i 0), hnode 0, hpred 0]
  · have hn_ge2 : 2 ≤ n := hn2
    let pref (k : ℕ) : List (AnonEvent n) :=
      ((List.finRange n).take k).map (AnonEvent.mk .clockwise)
    have hpref_step (j : ℕ) (hj : j < n) :
        pref (j + 1) = pref j ++ [⟨.clockwise, ⟨j, hj⟩⟩] ∧
          P.exec cfg (pref (j + 1)) = P.step ⟨.clockwise, ⟨j, hj⟩⟩ (P.exec cfg (pref j)) := by
      have htake : (List.finRange n).take (j + 1) = (List.finRange n).take j ++ [⟨j, hj⟩] := by
        rw [List.take_add_one]
        simp only [List.length_finRange, hj, List.getElem?_eq_getElem, List.getElem_finRange,
          Option.toList_some, Fin.cast_mk]
      have hp : pref (j + 1) = pref j ++ [⟨.clockwise, ⟨j, hj⟩⟩] := by
        simp only [pref, htake, List.map_append, List.map]
      exact ⟨hp, by simp only [hp, exec, List.foldl_append, List.foldl]⟩
    have hbase : (P.lts n).MTr cfg (pref 1) (P.exec cfg (pref 1)) ∧
        ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred 1
          (P.exec cfg (pref 1)) := by
      let z : Fin n := ⟨0, hn_pos⟩
      have hz0 : z.val = 0 := rfl
      obtain ⟨hp1, hex1⟩ := hpref_step 0 hn_pos
      have hz_pred_val : (z - 1).val = n - 1 := by rw [fin_sub_one_val, hz0]; rfl
      have hen : cfg.Enabled ⟨.clockwise, z⟩ := by
        simp only [AnonAsyncConfig.Enabled, hsucc (z - 1), ne_eq, reduceCtorEq, not_false_iff]
      obtain ⟨hsn, hsp, hss⟩ := P.step_clockwise_of_cons (t := z) (hsucc (z - 1))
      rw [hex1, hp1]
      dsimp only [pref, List.take_zero, List.map, List.nil_append, exec, List.foldl, ClockWaveInv]
      refine ⟨LTS.MTr.single (P.lts n) ⟨hen, rfl⟩, fun i => ?_, fun i => ?_, fun i => ?_⟩
      · rw [hsn i, hnode z, hnode i]
        simp only [Fin.ext_iff, hz0]; split_ifs <;> first | rfl | omega
      · rw [hsp i, hnode z, hpred z, hpred i]
        simp only [Fin.ext_iff, hz0]; split_ifs <;> first | rfl | omega
      · rw [hss i, hnode z, hsucc i]
        simp only [Fin.ext_iff, hz0, hz_pred_val]
        split_ifs <;> first | rfl | omega | exact List.append_nil _
    have hstep_inv : ∀ k (hk : 1 ≤ k) (hkn : k < n - 1),
        (P.lts n).MTr cfg (pref k) (P.exec cfg (pref k)) ∧
          ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred k
            (P.exec cfg (pref k)) →
        (P.lts n).MTr cfg (pref (k + 1)) (P.exec cfg (pref (k + 1))) ∧
          ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred (k + 1)
            (P.exec cfg (pref (k + 1))) := by
      intro k hk hkn ⟨hmtr, hInv⟩
      let c := P.exec cfg (pref k)
      change ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred k c at hInv
      have hkn' : k < n := by omega
      let tk : Fin n := ⟨k, hkn'⟩
      have htk_val : tk.val = k := rfl
      obtain ⟨htk_pred_val, hc_pred, hc_node, hc_tk_pred, hen⟩ :=
        clockWaveInv_at hk c tk htk_val hInv
      obtain ⟨hInode, hIpred, hIsucc⟩ := hInv
      obtain ⟨hpref_succ, hexec_succ⟩ := hpref_step k hkn'
      obtain ⟨hsn, hsp, hss⟩ := P.step_clockwise_of_cons hc_pred
      dsimp only [ClockWaveInv]
      refine ⟨?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
      · rw [hexec_succ, hpref_succ]
        exact hmtr.stepR (P.lts n) ⟨hen, rfl⟩
      · rw [hexec_succ, hsn i, hc_node, hInode i]
        simp only [Fin.ext_iff, htk_val]; split_ifs <;> first | rfl | omega
      · rw [hexec_succ, hsp i, hc_node, hc_tk_pred, hIpred i]
        simp only [Fin.ext_iff, htk_val]; split_ifs <;> first | rfl | omega
      · rw [hexec_succ, hss i, hc_node, hIsucc i]
        simp only [Fin.ext_iff, htk_val, htk_pred_val]
        split_ifs <;> first | rfl | omega | exact List.append_nil _
    have hpenult : ∀ d : ℕ, (hd : d ≤ n - 2) →
        (P.lts n).MTr cfg (pref (1 + d)) (P.exec cfg (pref (1 + d))) ∧
          ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred (1 + d)
            (P.exec cfg (pref (1 + d))) := by
      intro d hd
      induction d with
      | zero => exact hbase
      | succ d ih => exact hstep_inv (1 + d) (by omega) (by omega) (ih (by omega))
    have h1n : 1 + (n - 2) = n - 1 := by omega
    obtain ⟨hmtr_last, hInv_last⟩ := hpenult (n - 2) le_rfl
    rw [h1n] at hmtr_last hInv_last
    let c := P.exec cfg (pref (n - 1))
    change ClockWaveInv s out.nextState m ms out.toSucc cp out.toPred (n - 1) c at hInv_last
    have hlast_lt : n - 1 < n := by omega
    let tlast : Fin n := ⟨n - 1, hlast_lt⟩
    have htlast_val : tlast.val = n - 1 := rfl
    obtain ⟨htlast_pred_val, hc_pred, hc_node, hc_tlast_pred, hen⟩ :=
      clockWaveInv_at (by omega) c tlast htlast_val hInv_last
    obtain ⟨hInode, hIpred, hIsucc⟩ := hInv_last
    have hwave_eq : clockwiseWave n = pref ((n - 1) + 1) := congrArg (List.map _)
      (List.take_of_length_le (by simp only [List.length_finRange]; omega)).symm
    obtain ⟨hwave_split, hexec_last⟩ := hpref_step (n - 1) hlast_lt
    rw [← hwave_eq] at hwave_split hexec_last
    obtain ⟨hsn, hsp, hss⟩ := P.step_clockwise_of_cons hc_pred
    dsimp only [AnonAsyncConfig.IsUniform]
    refine ⟨?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · rw [hexec_last, hwave_split]
      exact hmtr_last.stepR (P.lts n) ⟨hen, rfl⟩
    · rw [hexec_last, hsn i, hc_node, hInode i]
      simp only [Fin.ext_iff, htlast_val]; split_ifs <;> first | rfl | omega
    · rw [hexec_last, hss i, hc_node, hIsucc i]
      simp only [Fin.ext_iff, htlast_val, htlast_pred_val]
      split_ifs <;> first | rfl | omega | exact List.append_nil _
    · rw [hexec_last, hsp i, hc_node, hc_tlast_pred, hIpred i]
      simp only [Fin.ext_iff, htlast_val]; split_ifs <;> first | rfl | omega

/-- Dual protocol flipping `clockwise` and `counter`, used to transfer `mtr_clockwiseWave_uniform`
to `counterWave` by ring reversal `i ↦ -i` without duplicating the wave proof. -/
private def dual (P : AnonAsyncProtocol S M) : AnonAsyncProtocol S M where
  init := P.init
  initToPred := P.initToSucc
  initToSucc := P.initToPred
  recvFromPred s m :=
    let out := P.recvFromSucc s m
    ⟨out.nextState, out.toSucc, out.toPred⟩
  recvFromSucc s m :=
    let out := P.recvFromPred s m
    ⟨out.nextState, out.toSucc, out.toPred⟩
  isLeader := P.isLeader

private def reflectConfig {n : ℕ} (cfg : AnonAsyncConfig n S M) :
    AnonAsyncConfig n S M where
  node i := cfg.node (-i)
  chanSucc i := cfg.chanPred (-i)
  chanPred i := cfg.chanSucc (-i)

private theorem reflectConfig_involutive {n : ℕ} (cfg : AnonAsyncConfig n S M) :
    reflectConfig (reflectConfig cfg) = cfg := by
  simp only [reflectConfig, neg_neg]

private theorem update_neg {n : ℕ} {α : Type*} (f : Fin n → α) (a : Fin n) (v : α)
    (i : Fin n) :
    Function.update (fun j => f (-j)) a v (-i) = Function.update f (-a) v i := by
  by_cases h : i = -a
  · subst h
    simp only [neg_neg, Function.update_self]
  · have h' : -i ≠ a := fun heq => h (by rw [← heq, neg_neg])
    simp only [Function.update_of_ne h', Function.update_of_ne h, neg_neg]

private theorem step_counter_eq_dual {n : ℕ} [NeZero n] (t : Fin n)
    (cfg : AnonAsyncConfig n S M) :
    P.step ⟨.counter, t⟩ cfg =
      reflectConfig (P.dual.step ⟨.clockwise, -t⟩ (reflectConfig cfg)) := by
  have hsub : -t - 1 = -(t + 1) := by
    rw [sub_eq_add_neg, neg_add]
  simp only [step, dual, reflectConfig, hsub, neg_neg]
  cases hq : cfg.chanPred (t + 1) with
  | nil => exact (reflectConfig_involutive cfg).symm
  | cons m rest =>
    dsimp only [reflectConfig]
    refine AnonAsyncConfig.ext (funext fun i => ?_) (funext fun i => ?_)
      (funext fun i => ?_)
    · simpa only [neg_neg] using
        (update_neg cfg.node (-t) (P.recvFromSucc (cfg.node t) m).nextState i).symm
    · simpa only [neg_neg] using
        (update_neg cfg.chanSucc (-t) (cfg.chanSucc t ++ (P.recvFromSucc (cfg.node t) m).toSucc)
          i).symm
    · have h1 : Function.update (fun j => cfg.chanPred (-j)) (-(t + 1)) rest =
          fun j => Function.update cfg.chanPred (t + 1) rest (-j) :=
        funext fun j => by simpa only [neg_neg] using update_neg cfg.chanPred (-(t + 1)) rest (-j)
      rw [h1]
      simpa only [neg_neg] using
        (update_neg (Function.update cfg.chanPred (t + 1) rest) (-t)
          (Function.update cfg.chanPred (t + 1) rest t ++ (P.recvFromSucc (cfg.node t) m).toPred)
          i).symm

private theorem enabled_counter_iff_dual {n : ℕ} [NeZero n] (t : Fin n)
    (cfg : AnonAsyncConfig n S M) :
    cfg.Enabled ⟨.counter, t⟩ ↔ (reflectConfig cfg).Enabled ⟨.clockwise, -t⟩ := by
  have hsub : -t - 1 = -(t + 1) := by
    rw [sub_eq_add_neg, neg_add]
  simp only [AnonAsyncConfig.Enabled, reflectConfig, hsub, neg_neg]

private theorem mtr_reflect_counter {n : ℕ} [NeZero n] {xs : List (Fin n)}
    {c₁ c₂ : AnonAsyncConfig n S M}
    (hmtr : (P.dual.lts n).MTr c₁ (xs.map (AnonEvent.mk .clockwise)) c₂) :
    (P.lts n).MTr (reflectConfig c₁) (xs.map fun i => ⟨.counter, -i⟩) (reflectConfig c₂) := by
  induction xs generalizing c₁ with
  | nil =>
    cases hmtr
    exact LTS.MTr.refl
  | cons i is ih =>
    simp only [List.map_cons] at hmtr ⊢
    rcases LTS.MTr.cons_iff.mp hmtr with ⟨cmid, ⟨hen, rfl⟩, hrest⟩
    refine LTS.MTr.stepL ⟨?_, ?_⟩ (ih hrest)
    · rw [enabled_counter_iff_dual (-i) (reflectConfig c₁), neg_neg, reflectConfig_involutive]
      exact hen
    · rw [P.step_counter_eq_dual (-i) (reflectConfig c₁), neg_neg, reflectConfig_involutive]

private theorem exec_counterWave_eq_dual {n : ℕ} [NeZero n] (cfg : AnonAsyncConfig n S M) :
    P.exec cfg (counterWave n) =
      reflectConfig (P.dual.exec (reflectConfig cfg) (clockwiseWave n)) := by
  suffices ∀ (xs : List (Fin n)) (c : AnonAsyncConfig n S M),
      P.exec c (xs.map fun i => ⟨.counter, -i⟩) =
        reflectConfig (P.dual.exec (reflectConfig c) (xs.map (AnonEvent.mk .clockwise))) from
    this (List.finRange n) cfg
  intro xs c
  induction xs generalizing c with
  | nil => exact (reflectConfig_involutive c).symm
  | cons i is ih =>
    simp only [List.map_cons, exec_cons]
    have hstep := P.step_counter_eq_dual (-i) c
    rw [neg_neg] at hstep
    rw [hstep, ih, reflectConfig_involutive]

private theorem mtr_counterWave_uniform {n : ℕ} [NeZero n] {cfg : AnonAsyncConfig n S M}
    {s : S} {m : M} {cs mp : List M} (huni : cfg.IsUniform s cs (m :: mp)) :
    (P.lts n).MTr cfg (counterWave n) (P.exec cfg (counterWave n)) ∧
      (P.exec cfg (counterWave n)).IsUniform
        (P.recvFromSucc s m).nextState
        (cs ++ (P.recvFromSucc s m).toSucc)
        (mp ++ (P.recvFromSucc s m).toPred) := by
  have hrefl : (reflectConfig cfg).IsUniform s (m :: mp) cs :=
    ⟨fun i => huni.1 (-i), fun i => huni.2.2 (-i), fun i => huni.2.1 (-i)⟩
  obtain ⟨hmtr_d, huni_d⟩ := P.dual.mtr_clockwiseWave_uniform hrefl
  refine ⟨?_, ?_⟩
  · have htr := P.mtr_reflect_counter hmtr_d
    rwa [reflectConfig_involutive, ← P.exec_counterWave_eq_dual cfg] at htr
  · rw [P.exec_counterWave_eq_dual cfg]
    exact ⟨fun i => huni_d.1 (-i), fun i => huni_d.2.2 (-i), fun i => huni_d.2.1 (-i)⟩

/-- Helper step for sequential FIFO waves on `Fin n`: from any uniform configuration, executing a
clockwise wave (when clockwise queues are nonempty) or a counter-clockwise wave (when
counter-clockwise queues are nonempty) is a valid multi-step `LTS.MTr` trace that leaves the ring
in a uniform configuration. -/
theorem mtr_rotWave_uniform {n : ℕ} [NeZero n] {cfg : AnonAsyncConfig n S M}
    {s : S} {cs cp : List M} (huni : cfg.IsUniform s cs cp) (d : RingDir) :
    (match d with
      | .clockwise => cs ≠ [] → (P.lts n).MTr cfg (clockwiseWave n) (P.exec cfg (clockwiseWave n))
      | .counter => cp ≠ [] → (P.lts n).MTr cfg (counterWave n) (P.exec cfg (counterWave n))) ∧
    ∃ s' cs' cp',
      (P.exec cfg
        (match d with | .clockwise => clockwiseWave n | .counter => counterWave n)).IsUniform
        s' cs' cp' := by
  cases d with
  | clockwise =>
    cases cs with
    | nil =>
      refine ⟨fun h => absurd rfl h, s, [], cp, ?_⟩
      rwa [clockwiseWave, P.exec_map_eq_self fun i => by simp only [step, huni.2.1 (i - 1)]]
    | cons m ms =>
      obtain ⟨hmtr, huni'⟩ := P.mtr_clockwiseWave_uniform huni
      exact ⟨fun _ => hmtr, _, _, _, huni'⟩
  | counter =>
    cases cp with
    | nil =>
      refine ⟨fun h => absurd rfl h, s, cs, [], ?_⟩
      rwa [counterWave, P.exec_map_eq_self fun i => by simp only [step, huni.2.2 (-i + 1)]]
    | cons m mp =>
      obtain ⟨hmtr, huni'⟩ := P.mtr_counterWave_uniform huni
      exact ⟨fun _ => hmtr, _, _, _, huni'⟩

/-- A sequential-FIFO-wave symmetry step on anonymous oriented rings `Fin n` (a step towards
[Angluin][Angluin1980b], not the general asynchronous processor-network endpoint): from
`P.initConfig n` (`2 ≤ n`), for every target wave count `W` there exists an enabled multi-step FIFO
trace `sched` in `P.lts n` that either completes `W` nonempty waves or reaches a quiescent terminal
configuration (`(P.lts n).IsTerminal`), with leader cardinality `≠ 1`. -/
theorem exists_rotWave_trace_leaders_card_ne_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (W : ℕ) :
    ∃ sched cfg,
      (P.lts n).MTr (P.initConfig n) sched cfg ∧
      (W * n ≤ sched.length ∨ (P.lts n).IsTerminal cfg) ∧
      (P.configLeaders cfg).card ≠ 1 := by
  have hbuild : ∀ w : ℕ, ∃ sched cfg s cs cp,
      (P.lts n).MTr (P.initConfig n) sched cfg ∧
      cfg.IsUniform s cs cp ∧
      (w * n ≤ sched.length ∨ (cs = [] ∧ cp = [])) := by
    intro w
    induction w with
    | zero =>
      exact ⟨[], P.initConfig n, P.init, P.initToSucc, P.initToPred, LTS.MTr.refl,
        ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, Or.inl (by simp)⟩
    | succ w ih =>
      obtain ⟨sched, cfg, s, cs, cp, hmtr, huni, hlen_or_empty⟩ := ih
      rcases hlen_or_empty with hlen | ⟨hcs, hcp⟩
      · cases hcs_eq : cs with
        | cons m ms =>
          have huni' : cfg.IsUniform s (m :: ms) cp := hcs_eq ▸ huni
          obtain ⟨hw_mtr, hw_uni⟩ := P.mtr_clockwiseWave_uniform huni'
          refine ⟨sched ++ clockwiseWave n, P.exec cfg (clockwiseWave n), _, _, _,
            hmtr.comp (P.lts n) hw_mtr, hw_uni, Or.inl ?_⟩
          simp only [clockwiseWave, List.length_append, List.length_map, List.length_finRange,
            Nat.succ_mul]
          omega
        | nil =>
          cases hcp_eq : cp with
          | cons m mp =>
            have huni' : cfg.IsUniform s cs (m :: mp) := hcp_eq ▸ huni
            obtain ⟨hw_mtr, hw_uni⟩ := P.mtr_counterWave_uniform huni'
            refine ⟨sched ++ counterWave n, P.exec cfg (counterWave n), _, _, _,
              hmtr.comp (P.lts n) hw_mtr, hw_uni, Or.inl ?_⟩
            simp only [counterWave, List.length_append, List.length_map, List.length_finRange,
              Nat.succ_mul]
            omega
          | nil =>
            subst hcs_eq hcp_eq
            exact ⟨sched, cfg, s, [], [], hmtr, huni, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨sched, cfg, s, cs, cp, hmtr, huni, Or.inr ⟨hcs, hcp⟩⟩
  obtain ⟨sched, cfg, s, cs, cp, hmtr, huni, hdone⟩ := hbuild W
  refine ⟨sched, cfg, hmtr, ?_, ?_⟩
  · rcases hdone with hlen | ⟨hcs, hcp⟩
    · exact Or.inl hlen
    · right
      rintro ⟨dir, t⟩ cfg' ⟨hen, _⟩
      cases dir with
      | clockwise =>
        exact hen ((huni.2.1 (t - 1)).trans hcs)
      | counter =>
        exact hen ((huni.2.2 (t + 1)).trans hcp)
  · by_cases hs : P.isLeader s = true <;> simp [configLeaders, huni.1, hs]
    omega

end AnonAsyncProtocol

end Cslib.Distributed.RingElection
