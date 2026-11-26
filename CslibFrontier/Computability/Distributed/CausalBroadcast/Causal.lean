/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup

/-!
# Single-Group Vector-Clock Asynchronous Causal Broadcast Step

This module formalizes a static single-group, single-hop vector-clock causal broadcast (`CBCAST`)
protocol step toward #7297 (after Birman, Schiper, and Stephenson [BirmanSchiperStephenson1991],
§§4.2–4.3, §5.1, and the broadcast specifications of Hadzilacos and Toueg [HadzilacosToueg1994],
§§3.1, 3.3, 3.8–3.9) over an asynchronous message-passing labelled transition system (`Cslib.LTS`)
with arbitrary message reordering and arbitrary static crash-fault sets `F : Set P` (requiring no
`2t < n` majority or quorum assumption).

Each process `p : P` maintains a vector timestamp `vt : P → ℕ` (initially `0`), a multiset buffer
`pending` of received but not yet deliverable packets, and its chronological delivery log
`delivered : List (Packet P V)`.

* **Broadcast:** To broadcast `payload : V`, an operational process `p` increments its own entry
  `vt' := Function.update vt p (vt p + 1)`, delivers `⟨p, vt', payload⟩` locally immediately, and
  places point-to-point copies `⟨q, ⟨p, vt', payload⟩⟩` in flight to all `q ≠ p` (a faulty sender
  `p ∈ F` may also crash mid-multicast via `BSSAction.crashBroadcast`, sending only to a subset
  `dests ⊆ Finset.univ.erase p` before halting).
* **Causal delivery condition (`Deliverable`):** Receiver `q ≠ s` delivers a buffered packet
  `pkt = ⟨s, ts, payload⟩` iff `ts s = vt q s + 1` and `∀ r ≠ s, ts r ≤ vt q r`, updating `vt q s`
  to `vt q s + 1` (which coincides with the coordinatewise supremum `vt q ⊔ ts`; see
  `sup_ts_eq_update_of_deliverable`).

## Model scope relative to primary sources

[BirmanSchiperStephenson1991] additionally studies dynamic group membership views (§4.1, §5.5),
token-holder view-synchronous `ABCAST` (§5.2), multicast stability and vector compression
(§§5.3–5.4), and overlapping process groups (§6). Here we formalize the static single-group
(`dests(m) = P`), single-hop `CBCAST` step of §§4.2–4.3 and §5.1 without diffusion or view-flush
forwarding. Because raw point-to-point multicast can be interrupted mid-send if a faulty sender
crashes (`BSSAction.crashBroadcast`), liveness at `q ∉ F` (`bss_live_of_packetSentTo`) is proved
under the causal-ancestor transmission hypothesis `PacketSentTo q` (specializing in
`bss_live_of_atomic_multicast` and `BSSSolvesAtomicMulticastCausalBroadcast` to liveness when
crashes occur between atomic multicast steps).

## Main definitions

* `Cslib.Distributed.CausalBroadcast.Packet`: broadcast packet carrying `sender`, vector timestamp
  `ts : P → ℕ`, and `payload`.
* `Cslib.Distributed.CausalBroadcast.vtWeight`: total timestamp weight `∑ r : P, vt r`.
* `Cslib.Distributed.CausalBroadcast.Deliverable`: Birman–Schiper–Stephenson causal delivery guard
  `pkt.ts s = vt s + 1 ∧ ∀ r ≠ s, pkt.ts r ≤ vt r`.
* `Cslib.Distributed.CausalBroadcast.NetMsg`,
  `Cslib.Distributed.CausalBroadcast.BSSProcState`,
  `Cslib.Distributed.CausalBroadcast.BSSState`,
  `Cslib.Distributed.CausalBroadcast.BSSAction`: network envelopes, local state, global state, and
  transition labels.
* `Cslib.Distributed.CausalBroadcast.bssInit`,
  `Cslib.Distributed.CausalBroadcast.bssStep`,
  `Cslib.Distributed.CausalBroadcast.bssLTS`: initial configuration, deterministic state step, and
  crash-fault `Cslib.LTS` parameterized by arbitrary `F : Set P`.
* `Cslib.Distributed.CausalBroadcast.BroadcastIn`,
  `Cslib.Distributed.CausalBroadcast.CausalStep`,
  `Cslib.Distributed.CausalBroadcast.CausalPrec`: packets broadcast along a trace and the
  broadcast causal precedence relation `b₁ ≺_bcast b₂`.
* `Cslib.Distributed.CausalBroadcast.BSSFair`,
  `Cslib.Distributed.CausalBroadcast.PacketSentTo`,
  `Cslib.Distributed.CausalBroadcast.BSSSolvesAtomicMulticastCausalBroadcast`: weak
  eventual-delivery fairness for non-crashed processes `q ∉ F`, packet transmission to `q`, and
  bundled single-group safety and atomic-multicast liveness predicate.

## Main results

* `Cslib.Distributed.CausalBroadcast.sup_ts_eq_update_of_deliverable`: under `Deliverable vt pkt`,
  `vt ⊔ pkt.ts = Function.update vt pkt.sender (vt pkt.sender + 1)`.
* `Cslib.Distributed.CausalBroadcast.bss_integrity`: single-group uniform integrity — every packet
  delivered at any process (faulty or correct) was previously broadcast by `pkt.sender`.
* `Cslib.Distributed.CausalBroadcast.bss_no_duplicates`: duplicate-free delivery (`delivered.Nodup`)
  at every process (faulty or correct).
* `Cslib.Distributed.CausalBroadcast.bss_causalPrec_iff_ts_lt`: exact vector-clock characterization
  `CausalPrec xl b₁ b₂ ↔ b₁.ts < b₂.ts` for broadcast packets in `bssLTS F`.
* `Cslib.Distributed.CausalBroadcast.bss_causal_delivery`: single-group uniform causal delivery
  order — at every process `q` (crashed or correct) that delivers `b₂`, any `b₁` with
  `CausalPrec xl b₁ b₂` was already delivered strictly earlier (`idxOf b₁ < idxOf b₂`).
* `Cslib.Distributed.CausalBroadcast.deliverable_stable_until_delivered`: once buffered and
  `Deliverable`, a packet remains buffered and `Deliverable` until delivered.
* `Cslib.Distributed.CausalBroadcast.bss_live_of_packetSentTo`,
  `Cslib.Distributed.CausalBroadcast.bss_live_of_atomic_multicast`, and
  `Cslib.Distributed.CausalBroadcast.bss_solves_atomicMulticast_causalBroadcast`: single-group
  crash-tolerant liveness under causal-ancestor packet transmission (`PacketSentTo`) or atomic
  multicast steps (`IsAtomicMulticastAction`) for any fault set `F : Set P` via strong induction on
  `vtWeight b.ts`.

## References

* [K. Birman, A. Schiper, P. Stephenson, *Lightweight causal and atomic group
  multicast*][BirmanSchiperStephenson1991]
* [V. Hadzilacos, S. Toueg, *A modular approach to fault-tolerant broadcasts and related
  problems*][HadzilacosToueg1994]
-/

public section

namespace Cslib.Distributed.CausalBroadcast

open Cslib Cslib.ωSequence

/-! ### Packets, vector timestamps, and causal deliverability -/

/-- A broadcast packet emitted in the Birman–Schiper–Stephenson `CBCAST` protocol
([BirmanSchiperStephenson1991], §5.1, p. 281): `sender` is the originating broadcaster, `ts` is
the vector timestamp `VT(m) : P → ℕ` assigned upon broadcast, and `payload` is the message body. -/
@[ext]
structure Packet (P V : Type*) where
  /-- Originating broadcaster process. -/
  sender : P
  /-- Vector timestamp `VT(m)` recording causal broadcast counts per sender. -/
  ts : P → ℕ
  /-- Application payload carried by the broadcast. -/
  payload : V

instance {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] :
    DecidableEq (Packet P V) :=
  fun a b => decidable_of_iff (a.sender = b.sender ∧ a.ts = b.ts ∧ a.payload = b.payload)
    ⟨fun ⟨h1, h2, h3⟩ => Packet.ext h1 h2 h3, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-- Total coordinate weight `∑ r : P, vt r` of a vector timestamp, measuring the size of a
broadcast's causal past for liveness induction. -/
@[expose]
def vtWeight {P : Type*} [Fintype P] (vt : P → ℕ) : ℕ :=
  ∑ r : P, vt r

/-- Strict vector-timestamp inequality `u < v` strictly increases `vtWeight`. -/
private theorem vtWeight_strictMono {P : Type*} [Fintype P] {u v : P → ℕ} (h : u < v) :
    vtWeight u < vtWeight v := by
  rw [Pi.lt_def] at h
  exact Finset.sum_lt_sum (fun r _ => h.1 r)
    (let ⟨r, hr⟩ := h.2; ⟨r, Finset.mem_univ r, hr⟩)

/-- The Birman–Schiper–Stephenson causal delivery guard ([BirmanSchiperStephenson1991], §5.1,
step 2, p. 281): a buffered packet `pkt` from `s = pkt.sender` is deliverable against local vector
time `vt` iff `pkt` is the next undelivered broadcast from `s` (`pkt.ts s = vt s + 1`) and the
recipient has already delivered all broadcasts from other senders `r ≠ s` that causally precede
`pkt` (`pkt.ts r ≤ vt r`). -/
@[expose]
def Deliverable {P V : Type*} (vt : P → ℕ) (pkt : Packet P V) : Prop :=
  pkt.ts pkt.sender = vt pkt.sender + 1 ∧ ∀ r, r ≠ pkt.sender → pkt.ts r ≤ vt r

instance {P V : Type*} [Fintype P] [DecidableEq P] (vt : P → ℕ) (pkt : Packet P V) :
    Decidable (Deliverable vt pkt) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Under `Deliverable vt pkt`, the coordinatewise `max` rule of [BirmanSchiperStephenson1991],
§4.3 (p. 280), coincides with incrementing `vt` only at `pkt.sender`. -/
theorem sup_ts_eq_update_of_deliverable {P V : Type*} [DecidableEq P] {vt : P → ℕ}
    {pkt : Packet P V} (h : Deliverable vt pkt) :
    vt ⊔ pkt.ts = Function.update vt pkt.sender (vt pkt.sender + 1) := by
  ext r
  rcases eq_or_ne r pkt.sender with rfl | hr
  · simp [h.1]
  · simp [Function.update_of_ne hr, h.2 r hr]

/-! ### Network state, actions, and transition system -/

/-- A point-to-point network message in flight to `dest` carrying broadcast `pkt`. -/
@[ext]
structure NetMsg (P V : Type*) where
  /-- Recipient process identity. -/
  dest : P
  /-- Broadcast packet in transit. -/
  pkt : Packet P V

instance {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] :
    DecidableEq (NetMsg P V) :=
  fun a b => decidable_of_iff (a.dest = b.dest ∧ a.pkt = b.pkt)
    ⟨fun ⟨h1, h2⟩ => NetMsg.ext h1 h2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Local state of a process in the Birman–Schiper–Stephenson `CBCAST` protocol. Note that protocol
guards and transitions inspect only `vt`, `pending`, and `halted`; `delivered` records the sequence
of locally delivered packets for specification. -/
@[ext]
structure BSSProcState (P V : Type*) where
  /-- Current vector timestamp `VT(p)` of delivered broadcasts per sender. -/
  vt : P → ℕ
  /-- Delay buffer of received packets awaiting causal delivery. -/
  pending : Multiset (Packet P V)
  /-- Chronological log of broadcasts delivered to the local application. -/
  delivered : List (Packet P V)
  /-- Whether this process has halted due to a crash fault. -/
  halted : Bool

instance {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] :
    DecidableEq (BSSProcState P V) :=
  fun a b => decidable_of_iff
    (a.vt = b.vt ∧ a.pending = b.pending ∧ a.delivered = b.delivered ∧ a.halted = b.halted)
    ⟨fun ⟨h1, h2, h3, h4⟩ => BSSProcState.ext h1 h2 h3 h4, fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Global asynchronous network state of the `CBCAST` protocol: unordered multiset `inFlight` of
point-to-point packets in transit and per-process local states `proc`. -/
@[ext]
structure BSSState (P V : Type*) where
  /-- Unordered multiset of point-to-point network packets currently in transit. -/
  inFlight : Multiset (NetMsg P V)
  /-- Local state of each process. -/
  proc : P → BSSProcState P V

instance {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V] :
    DecidableEq (BSSState P V) :=
  fun a b => decidable_of_iff (a.inFlight = b.inFlight ∧ a.proc = b.proc)
    ⟨fun ⟨h1, h2⟩ => BSSState.ext h1 h2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Initial configuration of the `CBCAST` protocol: empty channels, zero vector clocks, empty
delay buffers, empty delivery logs, and all processes operational (`halted = false`). -/
@[expose]
def bssInit (P V : Type*) : BSSState P V where
  inFlight := 0
  proc := fun _ => ⟨0, 0, [], false⟩

/-- Increment coordinate `p` of vector clock `vt` by `1`. -/
@[expose]
def bssNextTimestamp {P : Type*} [DecidableEq P] (vt : P → ℕ) (p : P) : P → ℕ :=
  Function.update vt p (vt p + 1)

/-- The `Packet` constructed when process `p` broadcasts `payload` in state `s`. -/
@[expose]
def bssBroadcastPacket {P V : Type*} [DecidableEq P] (s : BSSState P V) (p : P) (payload : V) :
    Packet P V :=
  ⟨p, bssNextTimestamp (s.proc p).vt p, payload⟩

/-- Execute an atomic broadcast by `p` of `payload`: increment `vt p`, deliver locally at `p`
immediately, and enqueue network copies to all `q ≠ p`. -/
@[expose]
def bssExecBroadcast {P V : Type*} [Fintype P] [DecidableEq P]
    (s : BSSState P V) (p : P) (payload : V) : BSSState P V :=
  let pkt := bssBroadcastPacket s p payload
  let out : Multiset (NetMsg P V) := (Finset.univ.erase p).val.map (fun q => ⟨q, pkt⟩)
  { inFlight := s.inFlight + out
    proc := Function.update s.proc p
      ⟨pkt.ts, (s.proc p).pending, (s.proc p).delivered ++ [pkt], (s.proc p).halted⟩ }

/-- Execute a crash-interrupted broadcast by a faulty process `p`: `p` increments `vt p`, delivers
locally, transmits copies only to `dests`, and halts. -/
@[expose]
def bssExecCrashBroadcast {P V : Type*} [DecidableEq P]
    (s : BSSState P V) (p : P) (dests : Finset P) (payload : V) : BSSState P V :=
  let pkt := bssBroadcastPacket s p payload
  let out : Multiset (NetMsg P V) := dests.val.map (fun q => ⟨q, pkt⟩)
  { inFlight := s.inFlight + out
    proc := Function.update s.proc p
      ⟨pkt.ts, (s.proc p).pending, (s.proc p).delivered ++ [pkt], true⟩ }

/-- Receive an in-flight network message `m` into `m.dest`'s `pending` delay buffer. -/
@[expose]
def bssExecRecv {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (s : BSSState P V) (m : NetMsg P V) : BSSState P V :=
  let q := m.dest
  { inFlight := s.inFlight.erase m
    proc := Function.update s.proc q
      ⟨(s.proc q).vt, m.pkt ::ₘ (s.proc q).pending, (s.proc q).delivered, (s.proc q).halted⟩ }

/-- Deliver a buffered packet `pkt` at `q`, incrementing `vt q pkt.sender` and appending `pkt` to
`delivered`. -/
@[expose]
def bssExecDeliver {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (s : BSSState P V) (q : P) (pkt : Packet P V) : BSSState P V :=
  let s₀ := pkt.sender
  let vt' := Function.update (s.proc q).vt s₀ ((s.proc q).vt s₀ + 1)
  { inFlight := s.inFlight
    proc := Function.update s.proc q
      ⟨vt', (s.proc q).pending.erase pkt, (s.proc q).delivered ++ [pkt], (s.proc q).halted⟩ }

/-- Halt process `p` due to a crash fault. -/
@[expose]
def bssExecCrash {P V : Type*} [DecidableEq P] (s : BSSState P V) (p : P) : BSSState P V :=
  { inFlight := s.inFlight
    proc := Function.update s.proc p
      ⟨(s.proc p).vt, (s.proc p).pending, (s.proc p).delivered, true⟩ }

/-- Transition labels of the `CBCAST` labelled transition system. -/
inductive BSSAction (P V : Type*) where
  /-- Process `p` broadcasts `payload` to all `q ≠ p`. -/
  | broadcast (p : P) (payload : V)
  /-- Faulty process `p ∈ F` crashes mid-multicast after sending `payload` only to `dests`. -/
  | crashBroadcast (p : P) (dests : Finset P) (payload : V)
  /-- Network message `m` arrives at `m.dest` and enters its delay buffer. -/
  | recv (m : NetMsg P V)
  /-- Process `q` causally delivers `pkt` from its delay buffer. -/
  | deliver (q : P) (pkt : Packet P V)
  /-- Faulty process `p ∈ F` crashes and halts. -/
  | crash (p : P)
  /-- Dummy stuttering step leaving the global state unchanged. -/
  | stutter

/-- Deterministic state-update function for `BSSAction`. -/
@[expose]
def bssStep {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (s : BSSState P V) : BSSAction P V → BSSState P V
  | .broadcast p payload => bssExecBroadcast s p payload
  | .crashBroadcast p dests payload => bssExecCrashBroadcast s p dests payload
  | .recv m => bssExecRecv s m
  | .deliver q pkt => bssExecDeliver s q pkt
  | .crash p => bssExecCrash s p
  | .stutter => s

/-- Guard predicate specifying when `act` is enabled in state `s` under crash-fault set `F`. -/
@[expose]
def BSSEnabled {P V : Type*} [Fintype P] [DecidableEq P]
    (F : Set P) (s : BSSState P V) : BSSAction P V → Prop
  | .broadcast p _ => (s.proc p).halted = false
  | .crashBroadcast p dests _ =>
      p ∈ F ∧ (s.proc p).halted = false ∧ dests ⊆ Finset.univ.erase p
  | .recv m => m ∈ s.inFlight ∧ (s.proc m.dest).halted = false
  | .deliver q pkt =>
      (s.proc q).halted = false ∧ pkt ∈ (s.proc q).pending ∧ Deliverable (s.proc q).vt pkt
  | .crash p => p ∈ F ∧ (s.proc p).halted = false
  | .stutter => True

instance {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (F : Set P) [DecidablePred (· ∈ F)] (s : BSSState P V) :
    DecidablePred (BSSEnabled F s) := fun act =>
  match act with
  | .broadcast _ _ => inferInstanceAs (Decidable (_ = _))
  | .crashBroadcast _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .recv _ => inferInstanceAs (Decidable (_ ∧ _))
  | .deliver _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .crash _ => inferInstanceAs (Decidable (_ ∧ _))
  | .stutter => isTrue trivial

/-- Labelled transition system of the Birman–Schiper–Stephenson `CBCAST` protocol for an arbitrary
crash-fault set `F : Set P` (with no cardinality restriction on `F`). -/
@[expose]
def bssLTS {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (F : Set P) : LTS (BSSState P V) (BSSAction P V) where
  Tr s act s' := BSSEnabled F s act ∧ s' = bssStep s act

/-- Fold a finite list of `BSSAction`s starting from `s₀`. -/
@[expose]
def bssRun {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (s₀ : BSSState P V) (xl : List (BSSAction P V)) : BSSState P V :=
  xl.foldl bssStep s₀

/-- Check whether every action in `xl` is enabled from `s₀` under fault set `F`. -/
@[expose]
def bssValidTrace {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (F : Set P) : BSSState P V → List (BSSAction P V) → Prop
  | _, [] => True
  | s, act :: xl => BSSEnabled F s act ∧ bssValidTrace F (bssStep s act) xl

instance instDecidableBSSValidTrace {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (F : Set P) [DecidablePred (· ∈ F)] (s : BSSState P V) :
    (xl : List (BSSAction P V)) → Decidable (bssValidTrace F s xl)
  | [] => isTrue trivial
  | act :: xl =>
      letI := instDecidableBSSValidTrace F (bssStep s act) xl
      inferInstanceAs (Decidable (BSSEnabled F s act ∧ bssValidTrace F (bssStep s act) xl))

/-- Equivalence between `LTS.MTr` on `bssLTS F` and `bssValidTrace` + `bssRun`. -/
theorem bssLTS_mTr_iff {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (F : Set P) (s₀ : BSSState P V) (xl : List (BSSAction P V)) (s : BSSState P V) :
    (bssLTS F).MTr s₀ xl s ↔ bssValidTrace F s₀ xl ∧ s = bssRun s₀ xl := by
  induction xl generalizing s₀ with
  | nil =>
    refine ⟨fun h => ?_, fun ⟨_, hs⟩ => hs ▸ .refl⟩
    cases h
    exact ⟨trivial, rfl⟩
  | cons act xl ih =>
    refine ⟨fun h => ?_, fun ⟨⟨hen, hv⟩, hs⟩ => .stepL ⟨hen, rfl⟩ ((ih _).mpr ⟨hv, hs⟩)⟩
    rcases h with _ | ⟨⟨hen, rfl⟩, hmtr⟩
    obtain ⟨hv, hs⟩ := (ih _).mp hmtr
    exact ⟨⟨hen, hv⟩, hs⟩

/-! ### Trace snapshots and causal precedence -/

/-- State after the first `i` actions of a trace starting from `bssInit P V`. -/
@[expose]
def bssStateAt {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (xl : List (BSSAction P V)) (i : ℕ) : BSSState P V :=
  bssRun (bssInit P V) (xl.take i)

/-- The `Packet` newly broadcast by `act` from state `s`, or `none` if `act` is not a broadcast. -/
@[expose]
def emittedPacket {P V : Type*} [DecidableEq P] (s : BSSState P V) :
    BSSAction P V → Option (Packet P V)
  | .broadcast p payload => some (bssBroadcastPacket s p payload)
  | .crashBroadcast p _ payload => some (bssBroadcastPacket s p payload)
  | _ => none

/-- Set of packets broadcast along the finite trace `xl` from `bssInit P V`. -/
@[expose]
def BroadcastIn {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (xl : List (BSSAction P V)) : Set (Packet P V) :=
  {b | ∃ (i : ℕ) (hi : i < xl.length), emittedPacket (bssStateAt xl i) xl[i] = some b}

/-- Direct (single-hop) causal relation between two packets broadcast along `xl`: either the same
process broadcast `b₁` strictly before `b₂`, or `b₂.sender` had already delivered `b₁` when it
broadcast `b₂` ([BirmanSchiperStephenson1991], §4.2, pp. 278–279; [HadzilacosToueg1994], §3.3,
p. 11). -/
@[expose]
def CausalStep {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (xl : List (BSSAction P V)) (b₁ b₂ : Packet P V) : Prop :=
  (∃ (i j : ℕ) (hi : i < xl.length) (hj : j < xl.length),
      i < j ∧
      emittedPacket (bssStateAt xl i) xl[i] = some b₁ ∧
      emittedPacket (bssStateAt xl j) xl[j] = some b₂ ∧
      b₁.sender = b₂.sender) ∨
  (b₁ ∈ BroadcastIn xl ∧
    ∃ (j : ℕ) (hj : j < xl.length),
      emittedPacket (bssStateAt xl j) xl[j] = some b₂ ∧
      b₁ ∈ ((bssStateAt xl j).proc b₂.sender).delivered)

/-- Broadcast causal precedence `b₁ ≺_bcast b₂`, the transitive closure of `CausalStep xl`. -/
@[expose]
def CausalPrec {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (xl : List (BSSAction P V)) : Packet P V → Packet P V → Prop :=
  Relation.TransGen (CausalStep xl)

section Invariants

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-! ### Trace-extension and monotonicity lemmas -/

private theorem bssRun_append (s₀ : BSSState P V) (xl yl : List (BSSAction P V)) :
    bssRun s₀ (xl ++ yl) = bssRun (bssRun s₀ xl) yl :=
  List.foldl_append

private theorem bssStateAt_append_of_le (xl : List (BSSAction P V)) (act : BSSAction P V)
    {i : ℕ} (hi : i ≤ xl.length) :
    bssStateAt (xl ++ [act]) i = bssStateAt xl i := by
  simp only [bssStateAt, List.take_append_of_le_length hi]

private theorem bssStateAt_length (xl : List (BSSAction P V)) :
    bssStateAt xl xl.length = bssRun (bssInit P V) xl := by
  simp only [bssStateAt, List.take_length]

private theorem bssAppendSingleton_at (xl : List (BSSAction P V)) (act : BSSAction P V)
    {i : ℕ} (hi : i < (xl ++ [act]).length) :
    (∃ hilt : i < xl.length,
      bssStateAt (xl ++ [act]) i = bssStateAt xl i ∧ (xl ++ [act])[i] = xl[i]) ∨
    (i = xl.length ∧
      bssStateAt (xl ++ [act]) i = bssRun (bssInit P V) xl ∧ (xl ++ [act])[i] = act) := by
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < xl.length
  · exact Or.inl ⟨hlt, bssStateAt_append_of_le xl act hlt.le, List.getElem_append_left hlt⟩
  · obtain rfl : i = xl.length := by omega
    exact Or.inr ⟨rfl, (bssStateAt_append_of_le xl act le_rfl).trans (bssStateAt_length xl),
      by simp⟩

private theorem broadcastIn_append (xl : List (BSSAction P V)) (act : BSSAction P V) :
    BroadcastIn (xl ++ [act]) =
      BroadcastIn xl ∪ {b | emittedPacket (bssRun (bssInit P V) xl) act = some b} := by
  ext b
  refine ⟨fun ⟨i, hi, hem⟩ => ?_, ?_⟩
  · rcases bssAppendSingleton_at xl act hi with ⟨hlt, hst, hget⟩ | ⟨_, hst, hget⟩
    · exact .inl ⟨i, hlt, by rwa [hst, hget] at hem⟩
    · exact .inr (by rwa [hst, hget] at hem)
  · rintro (⟨i, hi, hem⟩ | hem)
    · refine ⟨i, by simp; omega, ?_⟩
      rwa [bssStateAt_append_of_le xl act hi.le, List.getElem_append_left hi]
    · exact ⟨xl.length, by simp, by simpa [bssStateAt_append_of_le, bssStateAt_length] using hem⟩

private theorem broadcastIn_append_none {xl : List (BSSAction P V)} {act : BSSAction P V}
    (hnone : emittedPacket (bssRun (bssInit P V) xl) act = none) :
    BroadcastIn (xl ++ [act]) = BroadcastIn xl := by
  simp [broadcastIn_append, hnone]

private theorem broadcastIn_append_some {xl : List (BSSAction P V)} {act : BSSAction P V}
    {pkt : Packet P V} (hsome : emittedPacket (bssRun (bssInit P V) xl) act = some pkt) :
    BroadcastIn (xl ++ [act]) = insert pkt (BroadcastIn xl) := by
  rw [broadcastIn_append, hsome, Set.insert_eq, Set.union_comm]
  simp

/-- One step of `bssStep` never decreases any coordinate of any process's vector clock. -/
private theorem bssStep_vt_le (s : BSSState P V) (act : BSSAction P V) (q : P) :
    (s.proc q).vt ≤ ((bssStep s act).proc q).vt := by
  cases act with
  | broadcast p _ | crashBroadcast p _ _ | deliver p _ =>
    rcases eq_or_ne q p with rfl | hqp
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, bssExecDeliver,
        Function.update_self, bssBroadcastPacket, bssNextTimestamp]
      exact le_update_self_iff.mpr (Nat.le_succ _)
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, bssExecDeliver,
        Function.update_of_ne hqp, le_rfl]
  | recv _ | crash _ =>
    simp only [bssStep, bssExecRecv, bssExecCrash,
      Function.apply_update (fun _ => BSSProcState.vt), Function.update_eq_self, le_rfl]
  | stutter => exact le_rfl

/-- Multi-step vector-clock monotonicity along `bssRun`. -/
private theorem bssRun_vt_le (s : BSSState P V) (xl : List (BSSAction P V)) (q : P) :
    (s.proc q).vt ≤ ((bssRun s xl).proc q).vt := by
  induction xl generalizing s with
  | nil => exact le_rfl
  | cons act xl ih => exact le_trans (bssStep_vt_le s act q) (ih (bssStep s act))

/-- One step of `bssStep` only extends each process's `delivered` log by appending. -/
private theorem bssStep_delivered_prefix (s : BSSState P V) (act : BSSAction P V) (q : P) :
    (s.proc q).delivered <+: ((bssStep s act).proc q).delivered := by
  cases act with
  | broadcast p _ | crashBroadcast p _ _ | deliver p _ =>
    rcases eq_or_ne q p with rfl | hqp
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, bssExecDeliver,
        Function.update_self, List.prefix_append]
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, bssExecDeliver,
        Function.update_of_ne hqp, List.prefix_refl]
  | recv _ | crash _ =>
    simp only [bssStep, bssExecRecv, bssExecCrash,
      Function.apply_update (fun _ => BSSProcState.delivered), Function.update_eq_self,
      List.prefix_refl]
  | stutter => exact List.prefix_refl _

/-- Multi-step `delivered` prefix monotonicity along `bssRun`. -/
private theorem bssRun_delivered_prefix (s : BSSState P V) (xl : List (BSSAction P V)) (q : P) :
    (s.proc q).delivered <+: ((bssRun s xl).proc q).delivered := by
  induction xl generalizing s with
  | nil => exact List.prefix_refl _
  | cons act xl ih =>
    exact (bssStep_delivered_prefix s act q).trans (ih (bssStep s act))

/-! ### Inductive protocol invariant -/

/-- Inductive global invariant of the Birman–Schiper–Stephenson `CBCAST` protocol along any valid
trace `xl` reaching `s = bssRun (bssInit P V) xl`. -/
private structure BSSInv (F : Set P) (xl : List (BSSAction P V)) (s : BSSState P V) : Prop where
  /-- Only processes in `F` can halt. -/
  halted_mem : ∀ p, (s.proc p).halted = true → p ∈ F
  /-- Every in-flight packet was broadcast in `xl` by a process distinct from `m.dest`. -/
  inFlight_wf : ∀ m ∈ s.inFlight, m.pkt ∈ BroadcastIn xl ∧ m.pkt.sender ≠ m.dest
  /-- Every buffered packet at `q` was broadcast in `xl` by a process distinct from `q`. -/
  pending_wf : ∀ q pkt, pkt ∈ (s.proc q).pending → pkt ∈ BroadcastIn xl ∧ pkt.sender ≠ q
  /-- Every delivered packet at `q` was broadcast in `xl`. -/
  delivered_mem : ∀ q pkt, pkt ∈ (s.proc q).delivered → pkt ∈ BroadcastIn xl
  /-- Every delivered packet at `q` has timestamp bounded by `(s.proc q).vt`. -/
  ts_le_vt : ∀ q pkt, pkt ∈ (s.proc q).delivered → pkt.ts ≤ (s.proc q).vt
  /-- Each process's `delivered` log is duplicate-free. -/
  delivered_nodup : ∀ q, (s.proc q).delivered.Nodup
  /-- If `(s.proc q).vt r ≥ k ≥ 1`, then `q` has already delivered a packet from `r` with
  sender-coordinate `k`. -/
  exists_delivered_of_le_vt :
    ∀ q r k, 1 ≤ k → k ≤ (s.proc q).vt r →
      ∃ pkt ∈ (s.proc q).delivered, pkt.sender = r ∧ pkt.ts r = k
  /-- Every broadcast packet has positive sender-coordinate bounded by its sender's current `vt`. -/
  bcast_sender_bounds :
    ∀ b ∈ BroadcastIn xl, 1 ≤ b.ts b.sender ∧ b.ts b.sender ≤ (s.proc b.sender).vt b.sender
  /-- Every broadcast packet's non-sender coordinates reflect packets already delivered by its
  sender prior to the broadcast. -/
  bcast_emitted_spec :
    ∀ (i : ℕ) (hi : i < xl.length) (b : Packet P V),
      emittedPacket (bssStateAt xl i) xl[i] = some b →
      b.ts = bssNextTimestamp ((bssStateAt xl i).proc b.sender).vt b.sender
  /-- Two broadcasts by the same sender at steps `i < j` have strictly increasing timestamps and
  sender coordinates. -/
  same_sender_lt :
    ∀ (i j : ℕ) (hi : i < xl.length) (hj : j < xl.length) (b₁ b₂ : Packet P V),
      i < j →
      emittedPacket (bssStateAt xl i) xl[i] = some b₁ →
      emittedPacket (bssStateAt xl j) xl[j] = some b₂ →
      b₁.sender = b₂.sender →
      b₁.ts < b₂.ts ∧ b₁.ts b₁.sender < b₂.ts b₂.sender

private theorem bssInv_nil (F : Set P) : BSSInv F [] (bssInit P V) where
  halted_mem p hp := by simp [bssInit] at hp
  inFlight_wf m hm := by simp [bssInit] at hm
  pending_wf q pkt hp := by simp [bssInit] at hp
  delivered_mem q pkt hd := by simp [bssInit] at hd
  ts_le_vt q pkt hd := by simp [bssInit] at hd
  delivered_nodup q := by simp [bssInit]
  exists_delivered_of_le_vt q r k hk1 hkle := by
    simp only [bssInit, Pi.zero_apply] at hkle
    omega
  bcast_sender_bounds b hb := by simp [BroadcastIn] at hb
  bcast_emitted_spec i hi := by simp at hi
  same_sender_lt i j hi := by simp at hi

private theorem bssValidTrace_append_iff (F : Set P) (s₀ : BSSState P V)
    (xl : List (BSSAction P V)) (act : BSSAction P V) :
    bssValidTrace F s₀ (xl ++ [act]) ↔
      bssValidTrace F s₀ xl ∧ BSSEnabled F (bssRun s₀ xl) act := by
  induction xl generalizing s₀ with
  | nil => simp [bssValidTrace, bssRun]
  | cons a xl ih =>
    simp only [List.cons_append, bssValidTrace, bssRun, List.foldl_cons]
    exact (and_congr_right fun _ => ih (bssStep s₀ a)).trans and_assoc.symm

private theorem nonBroadcast_emitted_spec {F : Set P} {xl : List (BSSAction P V)}
    {s : BSSState P V} (hinv : BSSInv F xl s) {act : BSSAction P V}
    (hnone : emittedPacket (bssRun (bssInit P V) xl) act = none)
    (i : ℕ) (hi : i < (xl ++ [act]).length) (b : Packet P V)
    (hbi : emittedPacket (bssStateAt (xl ++ [act]) i) (xl ++ [act])[i] = some b) :
    b.ts = bssNextTimestamp ((bssStateAt (xl ++ [act]) i).proc b.sender).vt b.sender := by
  rcases bssAppendSingleton_at xl act hi with ⟨hlt, hst, hget⟩ | ⟨_, hst, hget⟩
  · rw [hst, hget] at hbi
    rw [hst]
    exact hinv.bcast_emitted_spec i hlt b hbi
  · rw [hst, hget, hnone] at hbi
    cases hbi

private theorem nonBroadcast_same_sender_lt {F : Set P} {xl : List (BSSAction P V)}
    {s : BSSState P V} (hinv : BSSInv F xl s) {act : BSSAction P V}
    (hnone : emittedPacket (bssRun (bssInit P V) xl) act = none)
    (i j : ℕ) (hi : i < (xl ++ [act]).length) (hj : j < (xl ++ [act]).length)
    (b₁ b₂ : Packet P V) (hij : i < j)
    (hbi : emittedPacket (bssStateAt (xl ++ [act]) i) (xl ++ [act])[i] = some b₁)
    (hbj : emittedPacket (bssStateAt (xl ++ [act]) j) (xl ++ [act])[j] = some b₂)
    (hsend : b₁.sender = b₂.sender) :
    b₁.ts < b₂.ts ∧ b₁.ts b₁.sender < b₂.ts b₂.sender := by
  rcases bssAppendSingleton_at xl act hj with ⟨hjlt, hst_j, hget_j⟩ | ⟨_, hst_j, hget_j⟩
  · have hilt : i < xl.length := Nat.lt_trans hij hjlt
    rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hilt), List.getElem_append_left hilt] at hbi
    rw [hst_j, hget_j] at hbj
    exact hinv.same_sender_lt i j hilt hjlt b₁ b₂ hij hbi hbj hsend
  · rw [hst_j, hget_j, hnone] at hbj
    cases hbj

/-! ### Step-preservation lemmas for `BSSInv` -/

/-- Shared invariant-preservation kernel when process `p` increments `vt pkt.sender` by `1` and
appends `pkt` to `(s.proc p).delivered` (covering both local broadcast and remote delivery). -/
private theorem bssInv_of_append_delivered {F : Set P} {xl : List (BSSAction P V)}
    {s s' : BSSState P V} (hinv : BSSInv F xl s) {act : BSSAction P V}
    {p : P} {pkt : Packet P V} {pend' : Multiset (Packet P V)} {halted' : Bool}
    (hs'_proc : s'.proc = Function.update s.proc p
      ⟨Function.update (s.proc p).vt pkt.sender ((s.proc p).vt pkt.sender + 1),
        pend', (s.proc p).delivered ++ [pkt], halted'⟩)
    (hB_sub : BroadcastIn xl ⊆ BroadcastIn (xl ++ [act]))
    (hpkt_mem : pkt ∈ BroadcastIn (xl ++ [act]))
    (hhalted : halted' = true → p ∈ F)
    (hinFlight : ∀ m ∈ s'.inFlight, m.pkt ∈ BroadcastIn (xl ++ [act]) ∧ m.pkt.sender ≠ m.dest)
    (hpend : ∀ b ∈ pend', b ∈ BroadcastIn (xl ++ [act]) ∧ b.sender ≠ p)
    (hpkt_ts_sender : pkt.ts pkt.sender = (s.proc p).vt pkt.sender + 1)
    (hpkt_ts_le : pkt.ts ≤ Function.update (s.proc p).vt pkt.sender ((s.proc p).vt pkt.sender + 1))
    (hbcast_bounds : ∀ b ∈ BroadcastIn (xl ++ [act]),
      1 ≤ b.ts b.sender ∧ b.ts b.sender ≤ (s'.proc b.sender).vt b.sender)
    (hemitted : ∀ (i : ℕ) (hi : i < (xl ++ [act]).length) (b : Packet P V),
      emittedPacket (bssStateAt (xl ++ [act]) i) (xl ++ [act])[i] = some b →
      b.ts = bssNextTimestamp ((bssStateAt (xl ++ [act]) i).proc b.sender).vt b.sender)
    (hsame : ∀ (i j : ℕ) (hi : i < (xl ++ [act]).length) (hj : j < (xl ++ [act]).length)
      (b₁ b₂ : Packet P V), i < j →
      emittedPacket (bssStateAt (xl ++ [act]) i) (xl ++ [act])[i] = some b₁ →
      emittedPacket (bssStateAt (xl ++ [act]) j) (xl ++ [act])[j] = some b₂ →
      b₁.sender = b₂.sender → b₁.ts < b₂.ts ∧ b₁.ts b₁.sender < b₂.ts b₂.sender) :
    BSSInv F (xl ++ [act]) s' where
  halted_mem q hq := by
    rw [hs'_proc] at hq
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self] at hq; exact hhalted hq
    · rw [Function.update_of_ne hqp] at hq; exact hinv.halted_mem q hq
  inFlight_wf := hinFlight
  pending_wf q b hb := by
    rw [hs'_proc] at hb
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self] at hb; exact hpend b hb
    · rw [Function.update_of_ne hqp] at hb
      exact ⟨hB_sub (hinv.pending_wf q b hb).1, (hinv.pending_wf q b hb).2⟩
  delivered_mem q b hb := by
    rw [hs'_proc] at hb
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self, List.mem_append, List.mem_singleton] at hb
      exact hb.elim (fun h => hB_sub (hinv.delivered_mem q b h)) (· ▸ hpkt_mem)
    · rw [Function.update_of_ne hqp] at hb; exact hB_sub (hinv.delivered_mem q b hb)
  ts_le_vt q b hb := by
    rw [hs'_proc] at hb ⊢
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self, List.mem_append, List.mem_singleton] at hb ⊢
      exact hb.elim
        (fun h => le_trans (hinv.ts_le_vt q b h) (le_update_self_iff.mpr (Nat.le_succ _)))
        (· ▸ hpkt_ts_le)
    · rw [Function.update_of_ne hqp] at hb ⊢; exact hinv.ts_le_vt q b hb
  delivered_nodup q := by
    rw [hs'_proc]
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self, List.nodup_append, List.nodup_singleton, true_and]
      refine ⟨hinv.delivered_nodup q, fun b hb b' hb' hbeq => ?_⟩
      rw [hbeq, List.mem_singleton.mp hb'] at hb
      exact absurd (hpkt_ts_sender ▸ hinv.ts_le_vt q pkt hb pkt.sender) (Nat.not_succ_le_self _)
    · rw [Function.update_of_ne hqp]; exact hinv.delivered_nodup q
  exists_delivered_of_le_vt q r k hk1 hkle := by
    rw [hs'_proc] at hkle ⊢
    rcases eq_or_ne q p with rfl | hqp
    · simp only [Function.update_self, List.mem_append, List.mem_singleton] at hkle ⊢
      rcases eq_or_ne r pkt.sender with rfl | hrs
      · simp only [Function.update_self] at hkle
        rcases Nat.of_le_succ hkle with hlt | rfl
        · obtain ⟨b, hb, hbs, hbk⟩ := hinv.exists_delivered_of_le_vt q _ k hk1 hlt
          exact ⟨b, Or.inl hb, hbs, hbk⟩
        · exact ⟨pkt, Or.inr rfl, rfl, hpkt_ts_sender⟩
      · rw [Function.update_of_ne hrs] at hkle
        obtain ⟨b, hb, hbs, hbk⟩ := hinv.exists_delivered_of_le_vt q r k hk1 hkle
        exact ⟨b, Or.inl hb, hbs, hbk⟩
    · rw [Function.update_of_ne hqp] at hkle ⊢; exact hinv.exists_delivered_of_le_vt q r k hk1 hkle
  bcast_sender_bounds := hbcast_bounds
  bcast_emitted_spec := hemitted
  same_sender_lt := hsame

private theorem bssInv_step_broadcast {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hinv : BSSInv F xl s) (hs : s = bssRun (bssInit P V) xl)
    {p : P} {dests : Finset P} {payload : V} {newHalted : Bool}
    (hdests : dests ⊆ Finset.univ.erase p)
    (hhalted : newHalted = true → p ∈ F) :
    let pkt := bssBroadcastPacket s p payload
    let out : Multiset (NetMsg P V) := dests.val.map (fun q => ⟨q, pkt⟩)
    let s' : BSSState P V :=
      { inFlight := s.inFlight + out
        proc := Function.update s.proc p
          ⟨pkt.ts, (s.proc p).pending, (s.proc p).delivered ++ [pkt], newHalted⟩ }
    ∀ act, emittedPacket s act = some pkt → bssStep s act = s' →
      BSSInv F (xl ++ [act]) s' := by
  intro pkt out s' act hem _
  have hsome : emittedPacket (bssRun (bssInit P V) xl) act = some pkt := hs ▸ hem
  have hbcast_eq : BroadcastIn (xl ++ [act]) = insert pkt (BroadcastIn xl) :=
    broadcastIn_append_some hsome
  have hpkt_ts_p : pkt.ts p = (s.proc p).vt p + 1 := by
    simp [pkt, bssBroadcastPacket, bssNextTimestamp]
  have hvt_lt_pkt : (s.proc p).vt < pkt.ts := lt_update_self_iff.mpr (Nat.lt_succ_self _)
  refine bssInv_of_append_delivered hinv rfl
    (hbcast_eq ▸ Set.subset_insert pkt _) (hbcast_eq ▸ Set.mem_insert pkt _) hhalted
    (fun m hm => ?_)
    (fun b hb => ⟨hbcast_eq ▸ Set.mem_insert_of_mem pkt (hinv.pending_wf p b hb).1,
      (hinv.pending_wf p b hb).2⟩)
    hpkt_ts_p le_rfl (fun b hb => ?_) (fun i hi b hbi => ?_)
    (fun i j hi hj b₁ b₂ hij hbi hbj hsend => ?_)
  · rw [hbcast_eq]
    rcases Multiset.mem_add.mp hm with hm | hm
    · exact ⟨Set.mem_insert_of_mem pkt (hinv.inFlight_wf m hm).1, (hinv.inFlight_wf m hm).2⟩
    · obtain ⟨q, hq_val, rfl⟩ := Multiset.mem_map.mp hm
      exact ⟨Set.mem_insert pkt _,
        (Finset.ne_of_mem_erase (hdests (Finset.mem_def.mpr hq_val))).symm⟩
  · rw [hbcast_eq] at hb
    rcases hb with rfl | hb
    · have hpkt_s : pkt.sender = p := rfl
      simp only [s', hpkt_s, Function.update_self, hpkt_ts_p]; omega
    · obtain ⟨hb1, hble⟩ := hinv.bcast_sender_bounds b hb
      refine ⟨hb1, ?_⟩
      rcases eq_or_ne b.sender p with hbp | hbp
      · rw [hbp] at hble ⊢; simp only [s', Function.update_self, hpkt_ts_p]; omega
      · simpa [s', Function.update_of_ne hbp] using hble
  · rcases bssAppendSingleton_at xl act hi with ⟨hlt, hst, hget⟩ | ⟨_, hst, hget⟩
    · rw [hst, hget] at hbi; rw [hst]; exact hinv.bcast_emitted_spec i hlt b hbi
    · rw [hst, hget, hsome] at hbi; cases Option.some.inj hbi; rw [hst, ← hs]; rfl
  · rcases bssAppendSingleton_at xl act hj with ⟨hjlt, hst_j, hget_j⟩ | ⟨hjeq, hst_j, hget_j⟩
    · have hilt : i < xl.length := Nat.lt_trans hij hjlt
      rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hilt), List.getElem_append_left hilt] at hbi
      rw [hst_j, hget_j] at hbj
      exact hinv.same_sender_lt i j hilt hjlt b₁ b₂ hij hbi hbj hsend
    · have hilt : i < xl.length := hjeq ▸ hij
      rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hilt), List.getElem_append_left hilt] at hbi
      rw [hst_j, hget_j, hsome] at hbj
      cases Option.some.inj hbj
      have hb₁_mem : b₁ ∈ BroadcastIn xl := ⟨i, hilt, hbi⟩
      have hb₁_spec := hinv.bcast_emitted_spec i hilt b₁ hbi
      have hvt_mono : ((bssStateAt xl i).proc p).vt ≤ (s.proc p).vt := by
        simpa only [hs, bssStateAt, ← bssRun_append, List.take_append_drop] using
          bssRun_vt_le (bssStateAt xl i) (xl.drop i) p
      have hb₁_le_s : b₁.ts ≤ (s.proc p).vt := fun r => by
        rcases eq_or_ne r b₁.sender with rfl | hr
        · exact hsend ▸ (hinv.bcast_sender_bounds b₁ hb₁_mem).2
        · rw [hb₁_spec, bssNextTimestamp, Function.update_of_ne hr, hsend]; exact hvt_mono r
      refine ⟨lt_of_le_of_lt hb₁_le_s hvt_lt_pkt, ?_⟩
      have hle_p : b₁.ts p ≤ (s.proc p).vt p := hb₁_le_s p
      rw [hsend, show pkt.sender = p from rfl, hpkt_ts_p]
      omega

private theorem bssInv_of_vt_delivered_eq {F : Set P} {xl : List (BSSAction P V)}
    {s : BSSState P V} (hinv : BSSInv F xl s) {act : BSSAction P V}
    (hnone : emittedPacket (bssRun (bssInit P V) xl) act = none)
    (hvt : ∀ q, ((bssStep s act).proc q).vt = (s.proc q).vt)
    (hdeliv : ∀ q, ((bssStep s act).proc q).delivered = (s.proc q).delivered)
    (hhalted : ∀ q, ((bssStep s act).proc q).halted = true → q ∈ F)
    (hinFlight : ∀ m ∈ (bssStep s act).inFlight, m.pkt ∈ BroadcastIn xl ∧ m.pkt.sender ≠ m.dest)
    (hpending : ∀ q b, b ∈ ((bssStep s act).proc q).pending →
      b ∈ BroadcastIn xl ∧ b.sender ≠ q) :
    BSSInv F (xl ++ [act]) (bssStep s act) := by
  have hbcast_eq := broadcastIn_append_none hnone
  exact
    { halted_mem := hhalted
      inFlight_wf := fun m hm => hbcast_eq ▸ hinFlight m hm
      pending_wf := fun q b hb => hbcast_eq ▸ hpending q b hb
      delivered_mem := fun q b hb => hbcast_eq ▸ hinv.delivered_mem q b ((hdeliv q) ▸ hb)
      ts_le_vt := fun q b hb => (hvt q).symm ▸ hinv.ts_le_vt q b ((hdeliv q) ▸ hb)
      delivered_nodup := fun q => (hdeliv q).symm ▸ hinv.delivered_nodup q
      exists_delivered_of_le_vt := fun q r k hk1 hkle => by
        rw [hdeliv q]
        exact hinv.exists_delivered_of_le_vt q r k hk1 ((hvt q) ▸ hkle)
      bcast_sender_bounds := fun b hb => by
        rw [hvt b.sender]
        exact hinv.bcast_sender_bounds b (hbcast_eq ▸ hb)
      bcast_emitted_spec := nonBroadcast_emitted_spec hinv hnone
      same_sender_lt := nonBroadcast_same_sender_lt hinv hnone }

private theorem bssInv_of_validTrace {F : Set P} {xl : List (BSSAction P V)}
    (hv : bssValidTrace F (bssInit P V) xl) :
    BSSInv F xl (bssRun (bssInit P V) xl) := by
  induction xl using List.reverseRecOn with
  | nil => exact bssInv_nil F
  | append_singleton xl act ih =>
    obtain ⟨hv_xl, hen⟩ := (bssValidTrace_append_iff F (bssInit P V) xl act).mp hv
    have hinv := ih hv_xl
    set s := bssRun (bssInit P V) xl with hs_def
    rw [bssRun_append, ← hs_def]
    change BSSInv F (xl ++ [act]) (bssStep s act)
    cases act with
    | broadcast p payload =>
      exact bssInv_step_broadcast hinv hs_def (Finset.Subset.refl _)
        (fun h => hinv.halted_mem p h) (.broadcast p payload) rfl rfl
    | crashBroadcast p dests payload =>
      rcases hen with ⟨hpF, _, hdests⟩
      exact bssInv_step_broadcast hinv hs_def hdests
        (fun _ => hpF) (.crashBroadcast p dests payload) rfl rfl
    | recv m =>
      rcases hen with ⟨hm_in, _⟩
      obtain ⟨hm_bcast, hm_ne⟩ := hinv.inFlight_wf m hm_in
      refine bssInv_of_vt_delivered_eq hinv rfl
        (fun q => by simp only [bssStep, bssExecRecv,
          Function.apply_update (fun _ => BSSProcState.vt), Function.update_eq_self])
        (fun q => by simp only [bssStep, bssExecRecv,
          Function.apply_update (fun _ => BSSProcState.delivered), Function.update_eq_self])
        (fun q hq => hinv.halted_mem q (by
          simpa only [bssStep, bssExecRecv, Function.apply_update (fun _ => BSSProcState.halted),
            Function.update_eq_self] using hq))
        (fun m' hm' => hinv.inFlight_wf m' (Multiset.mem_of_mem_erase hm'))
        (fun q b hb => ?_)
      rcases eq_or_ne q m.dest with rfl | hq_dest
      · simp only [bssStep, bssExecRecv, Function.update_self, Multiset.mem_cons] at hb
        exact hb.elim (· ▸ ⟨hm_bcast, hm_ne⟩) (hinv.pending_wf _ b)
      · exact hinv.pending_wf q b
          (by simpa only [bssStep, bssExecRecv, Function.update_of_ne hq_dest] using hb)
    | deliver p pkt =>
      rcases hen with ⟨_, hpkt_pend, hdeliv⟩
      have hnone : emittedPacket (bssRun (bssInit P V) xl) (.deliver p pkt) = none := rfl
      have hbcast_eq := broadcastIn_append_none hnone
      refine bssInv_of_append_delivered hinv rfl hbcast_eq.symm.subset
        (hbcast_eq ▸ (hinv.pending_wf p pkt hpkt_pend).1)
        (hinv.halted_mem p)
        (fun m hm => hbcast_eq ▸ hinv.inFlight_wf m hm)
        (fun b hb => hbcast_eq ▸ hinv.pending_wf p b (Multiset.mem_of_mem_erase hb))
        hdeliv.1
        (fun r => by
          rcases eq_or_ne r pkt.sender with rfl | hrs
          · simp [hdeliv.1]
          · simp [Function.update_of_ne hrs, hdeliv.2 r hrs])
        (fun b hb => ⟨(hinv.bcast_sender_bounds b (hbcast_eq ▸ hb)).1,
          le_trans (hinv.bcast_sender_bounds b (hbcast_eq ▸ hb)).2
            (bssStep_vt_le s (.deliver p pkt) b.sender b.sender)⟩)
        (nonBroadcast_emitted_spec hinv hnone)
        (nonBroadcast_same_sender_lt hinv hnone)
    | crash p =>
      rcases hen with ⟨hpF, _⟩
      refine bssInv_of_vt_delivered_eq hinv rfl
        (fun q => by simp only [bssStep, bssExecCrash,
          Function.apply_update (fun _ => BSSProcState.vt), Function.update_eq_self])
        (fun q => by simp only [bssStep, bssExecCrash,
          Function.apply_update (fun _ => BSSProcState.delivered), Function.update_eq_self])
        (fun q hq => ?_)
        hinv.inFlight_wf
        (fun q b hb => hinv.pending_wf q b (by
          simpa only [bssStep, bssExecCrash, Function.apply_update (fun _ => BSSProcState.pending),
            Function.update_eq_self] using hb))
      rcases eq_or_ne q p with rfl | hqp
      · exact hpF
      · exact hinv.halted_mem q
          (by simpa only [bssStep, bssExecCrash, Function.update_of_ne hqp] using hq)
    | stutter =>
      exact bssInv_of_vt_delivered_eq hinv rfl (fun _ => rfl) (fun _ => rfl)
        hinv.halted_mem hinv.inFlight_wf hinv.pending_wf

private theorem bssInv_of_mTr {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s) : BSSInv F xl s := by
  obtain ⟨hv, rfl⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  exact bssInv_of_validTrace hv

/-! ### Integrity and duplicate freedom -/

/-- Single-group single-hop `CBCAST` uniform-integrity step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1, p. 281 and [HadzilacosToueg1994], §3.1, p. 10 & §3.8, p. 14):
in any execution of `bssLTS F` (for arbitrary `F : Set P`), every packet delivered at any process
`q` (faulty or correct) was broadcast earlier in the trace by `pkt.sender`. -/
theorem bss_integrity {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s) (q : P) {pkt : Packet P V}
    (hdeliv : pkt ∈ (s.proc q).delivered) :
    pkt ∈ BroadcastIn xl :=
  (bssInv_of_mTr hmtr).delivered_mem q pkt hdeliv

/-- Single-group single-hop `CBCAST` duplicate-freedom step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1, p. 281 and [HadzilacosToueg1994], §3.1, p. 10 & §3.8, p. 14):
in any reachable state of `bssLTS F` (for arbitrary `F : Set P`), every process `q`'s delivery log
`(s.proc q).delivered` contains no duplicate packets. -/
theorem bss_no_duplicates {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s) (q : P) :
    (s.proc q).delivered.Nodup :=
  (bssInv_of_mTr hmtr).delivered_nodup q

/-! ### Vector-clock characterization and causal delivery order -/

private theorem validTrace_take {F : Set P} {s₀ : BSSState P V} {xl : List (BSSAction P V)}
    (hv : bssValidTrace F s₀ xl) (i : ℕ) :
    bssValidTrace F s₀ (xl.take i) := by
  induction xl generalizing s₀ i with
  | nil => simp [bssValidTrace]
  | cons act xl ih =>
    cases i with
    | zero => simp [bssValidTrace]
    | succ i =>
      exact ⟨hv.1, ih hv.2 i⟩

private theorem broadcastIn_take_subset (xl : List (BSSAction P V)) (j : ℕ) :
    BroadcastIn (xl.take j) ⊆ BroadcastIn xl := by
  rintro b ⟨u, hu, hbu⟩
  simp only [List.length_take] at hu
  have htake_eq : (xl.take j).take u = xl.take u :=
    List.take_take.trans (by simp [Nat.min_eq_left (by omega : u ≤ j)])
  exact ⟨u, by omega, by simpa [bssStateAt, htake_eq, List.getElem_take] using hbu⟩

/-- If `q`'s clock after the prefix `xl.take j` covers the sender coordinate of a broadcast packet,
then `q` had delivered that packet by then. -/
private theorem mem_delivered_take_of_ts_le {F : Set P} {xl : List (BSSAction P V)}
    (hv : bssValidTrace F (bssInit P V) xl) {pkt : Packet P V} (hpkt : pkt ∈ BroadcastIn xl)
    (j : ℕ) {q : P} (hle : pkt.ts pkt.sender ≤ ((bssStateAt xl j).proc q).vt pkt.sender) :
    pkt ∈ ((bssStateAt xl j).proc q).delivered := by
  have hinv := bssInv_of_validTrace hv
  have hinv_j := bssInv_of_validTrace (validTrace_take hv j)
  obtain ⟨b, hb, hs, ht⟩ :=
    hinv_j.exists_delivered_of_le_vt q _ _ (hinv.bcast_sender_bounds pkt hpkt).1 hle
  obtain ⟨i, hi, hbi⟩ := broadcastIn_take_subset xl j (hinv_j.delivered_mem q b hb)
  obtain ⟨i', hi', hpi⟩ := hpkt
  rcases lt_trichotomy i i' with h | rfl | h
  · exact ((hinv.same_sender_lt i i' hi hi' b pkt h hbi hpi hs).2.ne (hs.symm ▸ ht)).elim
  · cases hbi.symm.trans hpi; exact hb
  · exact ((hinv.same_sender_lt i' i hi' hi pkt b h hpi hbi hs.symm).2.ne' (hs.symm ▸ ht)).elim

private theorem same_sender_coord_lt_of_ts_lt {F : Set P} {xl : List (BSSAction P V)}
    (hinv : BSSInv F xl (bssRun (bssInit P V) xl)) {b₁ b₂ : Packet P V}
    (hb₁ : b₁ ∈ BroadcastIn xl) (hb₂ : b₂ ∈ BroadcastIn xl)
    (hsend : b₁.sender = b₂.sender) (hlt : b₁.ts < b₂.ts) :
    b₁.ts b₁.sender < b₂.ts b₂.sender := by
  obtain ⟨i, hi, hbi⟩ := hb₁
  obtain ⟨j, hj, hbj⟩ := hb₂
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (hinv.same_sender_lt i j hi hj b₁ b₂ hij hbi hbj hsend).2
  · rw [hbi] at hbj; cases Option.some.inj hbj; exact absurd hlt (lt_irrefl _)
  · exact absurd hlt (lt_asymm (hinv.same_sender_lt j i hj hi b₂ b₁ hji hbj hbi hsend.symm).1)

private theorem causalStep_ts_lt {F : Set P} {xl : List (BSSAction P V)}
    (hv : bssValidTrace F (bssInit P V) xl) {b₁ b₂ : Packet P V}
    (hstep : CausalStep xl b₁ b₂) : b₁.ts < b₂.ts := by
  have hinv := bssInv_of_validTrace hv
  rcases hstep with ⟨i, j, hi, hj, hij, hbi, hbj, hsend⟩ | ⟨_, j, hj, hbj, hdel⟩
  · exact (hinv.same_sender_lt i j hi hj b₁ b₂ hij hbi hbj hsend).1
  · exact lt_of_le_of_lt ((bssInv_of_validTrace (validTrace_take hv j)).ts_le_vt _ b₁ hdel)
      (hinv.bcast_emitted_spec j hj b₂ hbj ▸ lt_update_self_iff.mpr (Nat.lt_succ_self _))

/-- Vector-clock causal-precedence characterization for single-group single-hop `CBCAST` (toward
#7297, after [BirmanSchiperStephenson1991], §4.3, p. 280): along any execution of `bssLTS F`, for
any two broadcast packets `b₁, b₂ ∈ BroadcastIn xl`, `b₁` causally precedes `b₂` iff
`b₁.ts < b₂.ts`. -/
theorem bss_causalPrec_iff_ts_lt {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s)
    {b₁ b₂ : Packet P V} (hb₁ : b₁ ∈ BroadcastIn xl) (hb₂ : b₂ ∈ BroadcastIn xl) :
    CausalPrec xl b₁ b₂ ↔ b₁.ts < b₂.ts := by
  obtain ⟨hv, rfl⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  have hinv := bssInv_of_validTrace hv
  refine ⟨fun hprec => ?_, fun hlt => ?_⟩
  · clear hb₁ hb₂
    induction hprec with
    | single hstep => exact causalStep_ts_lt hv hstep
    | tail _ hstep ih => exact lt_trans ih (causalStep_ts_lt hv hstep)
  obtain ⟨j, hj, hbj⟩ := hb₂
  by_cases hsend : b₁.sender = b₂.sender
  · obtain ⟨i, hi, hbi⟩ := hb₁
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact .single (Or.inl ⟨i, j, hi, hj, hij, hbi, hbj, hsend⟩)
    · cases hbi.symm.trans hbj; exact (lt_irrefl _ hlt).elim
    · exact absurd hlt (lt_asymm (hinv.same_sender_lt j i hj hi b₂ b₁ hji hbj hbi hsend.symm).1)
  refine .single (Or.inr ⟨hb₁, j, hj, hbj, mem_delivered_take_of_ts_le hv hb₁ j ?_⟩)
  have h := hlt.le b₁.sender
  rwa [hinv.bcast_emitted_spec j hj b₂ hbj, bssNextTimestamp, Function.update_of_ne hsend] at h

private theorem local_bcast_ts_le_vt {F : Set P} {xl : List (BSSAction P V)}
    (hinv : BSSInv F xl (bssRun (bssInit P V) xl)) {k : ℕ} (hk_lt_len : k < xl.length)
    {q : P} {payload : V} {b₁ : Packet P V} (hb₁ : b₁ ∈ BroadcastIn xl)
    (hts_lt : b₁.ts < (bssBroadcastPacket (bssStateAt xl k) q payload).ts)
    (hemit_k : emittedPacket (bssStateAt xl k) xl[k] =
      some (bssBroadcastPacket (bssStateAt xl k) q payload)) :
    b₁.ts b₁.sender ≤ ((bssStateAt xl k).proc q).vt b₁.sender := by
  by_cases hsend : b₁.sender = q
  · have hlt_coord :=
      same_sender_coord_lt_of_ts_lt hinv hb₁ ⟨k, hk_lt_len, hemit_k⟩ hsend hts_lt
    simp only [hsend, bssBroadcastPacket, bssNextTimestamp, Function.update_self] at hlt_coord ⊢
    omega
  · simpa [bssBroadcastPacket, bssNextTimestamp, Function.update_of_ne hsend] using
      (le_of_lt hts_lt) b₁.sender

/-- Single-group single-hop `CBCAST` uniform causal-delivery step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1, Safety, p. 282 and [HadzilacosToueg1994], §3.3 & §3.8, pp. 11,
15): in any execution of `bssLTS F` (for arbitrary `F : Set P`), if `b₁` causally precedes `b₂`
(`CausalPrec xl b₁ b₂`), then at every process `q : P` (faulty or correct) that has delivered `b₂`,
`b₁` has already been delivered at `q` strictly prior to `b₂`. -/
theorem bss_causal_delivery {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s)
    {b₁ b₂ : Packet P V} (hb₁ : b₁ ∈ BroadcastIn xl) (hb₂ : b₂ ∈ BroadcastIn xl)
    (hprec : CausalPrec xl b₁ b₂) (q : P) (hdel₂ : b₂ ∈ (s.proc q).delivered) :
    b₁ ∈ (s.proc q).delivered ∧
      (s.proc q).delivered.idxOf b₁ < (s.proc q).delivered.idxOf b₂ := by
  have hts_lt : b₁.ts < b₂.ts := (bss_causalPrec_iff_ts_lt hmtr hb₁ hb₂).mp hprec
  obtain ⟨hv, rfl⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  have hinv := bssInv_of_validTrace hv
  -- Consider the step `k` of `xl` at which `b₂` enters `delivered` at `q`.
  have hex : ∃ m, m ≤ xl.length ∧ b₂ ∈ ((bssStateAt xl m).proc q).delivered :=
    ⟨xl.length, le_rfl, by rwa [bssStateAt_length]⟩
  obtain ⟨hm_le, hm_del₂⟩ := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_add_one_of_ne_zero fun h => by
    rw [h] at hm_del₂; simp [bssStateAt, bssRun, bssInit] at hm_del₂
  have hk_lt_len : k < xl.length := by omega
  have hnot_del₂_k : b₂ ∉ ((bssStateAt xl k).proc q).delivered := fun h =>
    Nat.find_min hex (by omega : k < Nat.find hex) ⟨by omega, h⟩
  have htake : xl.take (k + 1) = xl.take k ++ [xl[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk_lt_len, Option.toList_some]
  have hen_k : BSSEnabled F (bssStateAt xl k) xl[k] :=
    ((bssValidTrace_append_iff F _ _ _).mp (htake ▸ validTrace_take hv (k + 1))).2
  replace hm_del₂ : b₂ ∈ ((bssStep (bssStateAt xl k) xl[k]).proc q).delivered := by
    rw [hk] at hm_del₂
    simpa only [bssStateAt, htake, bssRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
      using hm_del₂
  -- `b₁` was already delivered at `q` before step `k`.
  have hb₁_k : b₁ ∈ ((bssStateAt xl k).proc q).delivered := by
    refine mem_delivered_take_of_ts_le hv hb₁ k ?_
    cases hp : xl[k] with
    | broadcast p payload | crashBroadcast p _ payload =>
      rw [hp] at hm_del₂
      rcases eq_or_ne p q with rfl | hpq
      · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, Function.update_self,
          List.mem_append, List.mem_singleton, hnot_del₂_k, false_or] at hm_del₂
        subst hm_del₂
        exact local_bcast_ts_le_vt hinv hk_lt_len hb₁ hts_lt (by simp [hp, emittedPacket])
      · simp [bssStep, bssExecBroadcast, bssExecCrashBroadcast, Function.update_of_ne hpq.symm,
          hnot_del₂_k] at hm_del₂
    | deliver p pkt =>
      rw [hp] at hm_del₂ hen_k
      rcases eq_or_ne p q with rfl | hpq
      · simp only [bssStep, bssExecDeliver, Function.update_self, List.mem_append,
          List.mem_singleton, hnot_del₂_k, false_or] at hm_del₂
        rw [← hm_del₂] at hen_k
        by_cases hsend : b₁.sender = b₂.sender
        · have := same_sender_coord_lt_of_ts_lt hinv hb₁ hb₂ hsend hts_lt
          rw [hsend, hen_k.2.2.1] at this; rw [hsend]; omega
        · exact (hts_lt.le b₁.sender).trans (hen_k.2.2.2 b₁.sender hsend)
      · simp [bssStep, bssExecDeliver, Function.update_of_ne hpq.symm, hnot_del₂_k] at hm_del₂
    | recv _ | crash _ | stutter =>
      rw [hp] at hm_del₂
      exact (hnot_del₂_k (by
        simpa only [bssStep, bssExecRecv, bssExecCrash, Function.update_eq_self,
          Function.apply_update (fun _ => BSSProcState.delivered)] using hm_del₂)).elim
  -- `delivered` only grows by appending, and `b₂` is appended after step `k`.
  obtain ⟨tail, hl_eq⟩ : ((bssStateAt xl k).proc q).delivered <+:
      ((bssRun (bssInit P V) xl).proc q).delivered := by
    simpa only [bssStateAt, ← bssRun_append, List.take_append_drop] using
      bssRun_delivered_prefix (bssStateAt xl k) (xl.drop k) q
  rw [← hl_eq, List.idxOf_append_of_mem hb₁_k, List.idxOf_append_of_notMem hnot_del₂_k]
  exact ⟨List.mem_append_left _ hb₁_k, by have := List.idxOf_lt_length_of_mem hb₁_k; omega⟩

end Invariants

section Liveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-! ### Fairness and infinite-execution specification -/

/-- Weak eventual-delivery fairness for `bssLTS F` on an infinite execution `(ss, xs)`:
1. Every network packet `m` addressed to a non-faulty process `m.dest ∉ F` is eventually received.
2. Every buffered packet at `q ∉ F` that satisfies `Deliverable` is eventually delivered at `q`.
(See `deliverable_stable_until_delivered` showing `Deliverable` remains continuously enabled until
`pkt` is delivered.) -/
structure BSSFair (F : Set P) (ss : ωSequence (BSSState P V))
    (xs : ωSequence (BSSAction P V)) : Prop where
  /-- Fair point-to-point network reception at non-faulty destinations. -/
  fair_recv : ∀ m : NetMsg P V, m.dest ∉ F → ∀ k, m ∈ (ss k).inFlight →
    ∃ j, k ≤ j ∧ xs j = .recv m
  /-- Weak local delivery fairness at non-faulty processes. -/
  fair_deliver : ∀ q, q ∉ F → ∀ pkt k,
    pkt ∈ ((ss k).proc q).pending → Deliverable ((ss k).proc q).vt pkt →
    ∃ j, k ≤ j ∧ pkt ∈ ((ss j).proc q).delivered

/-- Packet `b` was emitted along `(ss, xs)` and its copy to `q` was placed in flight (or `b`
originated at `q` itself). -/
@[expose]
def PacketSentTo (q : P) (ss : ωSequence (BSSState P V)) (xs : ωSequence (BSSAction P V))
    (b : Packet P V) : Prop :=
  ∃ k, emittedPacket (ss k) (xs k) = some b ∧ (b.sender = q ∨ ⟨q, b⟩ ∈ (ss (k + 1)).inFlight)

/-- Causal precedence between packets along an infinite execution `(ss, xs)`. -/
@[expose]
def OmegaCausalPrec (_ss : ωSequence (BSSState P V)) (xs : ωSequence (BSSAction P V))
    (b₁ b₂ : Packet P V) : Prop :=
  ∃ N, b₁ ∈ BroadcastIn (xs.extract 0 N) ∧ b₂ ∈ BroadcastIn (xs.extract 0 N) ∧
    CausalPrec (xs.extract 0 N) b₁ b₂

private theorem extract_take_eq {α : Type*} (xs : ωSequence α) {i N : ℕ} (hi : i ≤ N) :
    (xs.extract 0 N).take i = xs.extract 0 i := by
  rw [← ωSequence.append_extract_extract (Nat.zero_le i) hi,
    List.take_left' (by simp [ωSequence.length_extract])]

private theorem omega_mTr_prefix {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) (n : ℕ) :
    (bssLTS F).MTr (bssInit P V) (xs.extract 0 n) (ss n) := by
  rw [← hinit]
  exact he.extract_mTr (Nat.zero_le n)

private theorem omega_vt_mono {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (he : (bssLTS F).OmegaExecution ss xs)
    {i j : ℕ} (hij : i ≤ j) (q : P) :
    ((ss i).proc q).vt ≤ ((ss j).proc q).vt := by
  rw [((bssLTS_mTr_iff F (ss i) (xs.extract i j) (ss j)).mp (he.extract_mTr hij)).2]
  exact bssRun_vt_le (ss i) (xs.extract i j) q

/-- Monotonicity of `delivered` along an `OmegaExecution` of `bssLTS F`: once `pkt` has been
delivered at `q` at step `i`, it remains in `((ss j).proc q).delivered` at every step `j ≥ i`. -/
theorem bss_omega_delivered_mono {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (he : (bssLTS F).OmegaExecution ss xs)
    {i j : ℕ} (hij : i ≤ j) {q : P} {pkt : Packet P V}
    (h : pkt ∈ ((ss i).proc q).delivered) :
    pkt ∈ ((ss j).proc q).delivered := by
  rw [((bssLTS_mTr_iff F (ss i) (xs.extract i j) (ss j)).mp (he.extract_mTr hij)).2]
  exact (bssRun_delivered_prefix (ss i) (xs.extract i j) q).subset h

/-! ### Stability of buffered deliverable packets -/

private theorem omega_pending_persist {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (he : (bssLTS F).OmegaExecution ss xs)
    {k j : ℕ} (hkj : k ≤ j) {q : P} {pkt : Packet P V}
    (hpend : pkt ∈ ((ss k).proc q).pending)
    (hnot_del : pkt ∉ ((ss j).proc q).delivered) :
    pkt ∈ ((ss j).proc q).pending := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
  induction d with
  | zero => simpa using hpend
  | succ d ih =>
    have hnot_d : pkt ∉ ((ss (k + d)).proc q).delivered := fun hd =>
      hnot_del (by rw [← Nat.add_assoc]; exact bss_omega_delivered_mono he (Nat.le_succ (k + d)) hd)
    have hpend_d : pkt ∈ ((ss (k + d)).proc q).pending := ih (Nat.le_add_right k d) hnot_d
    obtain ⟨_, hstep⟩ := he (k + d)
    rw [← Nat.add_assoc, hstep] at hnot_del ⊢
    cases hact : xs (k + d) <;> simp only [hact, bssStep, bssExecBroadcast, bssExecCrashBroadcast,
      bssExecRecv, bssExecDeliver, bssExecCrash, Function.update_apply] at hnot_del ⊢ <;>
      (try split_ifs at hnot_del ⊢) <;> simp_all [Multiset.mem_erase_of_ne]

private theorem vt_sender_lt_of_not_delivered {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {j : ℕ} {q : P} {pkt : Packet P V}
    (hpkt_in : pkt ∈ BroadcastIn (xs.extract 0 j))
    (hnot_del : pkt ∉ ((ss j).proc q).delivered) :
    ((ss j).proc q).vt pkt.sender < pkt.ts pkt.sender := by
  obtain ⟨hv, hrun⟩ := (bssLTS_mTr_iff F _ _ _).mp (omega_mTr_prefix hinit he j)
  have h := mem_delivered_take_of_ts_le hv hpkt_in (xs.extract 0 j).length (q := q)
  rw [bssStateAt_length, ← hrun] at h
  exact not_le.mp (mt h hnot_del)

/-- Once a buffered packet `pkt` at `q` satisfies `Deliverable` at step `k`, it remains buffered
and `Deliverable` at every subsequent step `j ≥ k` until `q` delivers `pkt`. -/
theorem deliverable_stable_until_delivered {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {q : P} {pkt : Packet P V} {k j : ℕ} (hkj : k ≤ j)
    (hpend : pkt ∈ ((ss k).proc q).pending) (hdeliv : Deliverable ((ss k).proc q).vt pkt)
    (hnot_del : pkt ∉ ((ss j).proc q).delivered) :
    pkt ∈ ((ss j).proc q).pending ∧ Deliverable ((ss j).proc q).vt pkt := by
  have hpend_j := omega_pending_persist he hkj hpend hnot_del
  have hvt_le := omega_vt_mono he hkj q
  refine ⟨hpend_j, ?_, fun r hr => le_trans (hdeliv.2 r hr) (hvt_le r)⟩
  have hlt := vt_sender_lt_of_not_delivered hinit he
    ((bssInv_of_mTr (omega_mTr_prefix hinit he j)).pending_wf q pkt hpend_j).1 hnot_del
  have hle : ((ss k).proc q).vt pkt.sender ≤ ((ss j).proc q).vt pkt.sender := hvt_le pkt.sender
  have h1 := hdeliv.1
  omega

private theorem broadcastIn_extract_mono (xs : ωSequence (BSSAction P V)) {M N : ℕ}
    (hMN : M ≤ N) :
    BroadcastIn (xs.extract 0 M : List (BSSAction P V)) ⊆
      BroadcastIn (xs.extract 0 N : List (BSSAction P V)) :=
  extract_take_eq xs hMN ▸ broadcastIn_take_subset (xs.extract 0 N) M

private theorem emittedPacket_extract {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {i N : ℕ} (hi : i < (xs.extract 0 N).length) :
    emittedPacket (bssStateAt (xs.extract 0 N) i) (xs.extract 0 N)[i] =
      emittedPacket (ss i) (xs i) := by
  simp only [ωSequence.length_extract, Nat.sub_zero] at hi
  obtain ⟨_, hrun⟩ := (bssLTS_mTr_iff F _ _ _).mp (omega_mTr_prefix hinit he i)
  simp [bssStateAt, extract_take_eq xs hi.le, ← hrun, hi]

private theorem emittedPacket_mem_broadcastIn {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {k : ℕ} {b : Packet P V}
    (hem : emittedPacket (ss k) (xs k) = some b) :
    b ∈ BroadcastIn (xs.extract 0 (k + 1)) :=
  ⟨k, by simp, (emittedPacket_extract hinit he _).trans hem⟩

private theorem causalPrec_extract_mono {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {M N : ℕ} (hMN : M ≤ N)
    {b₁ b₂ : Packet P V}
    (hb₁ : b₁ ∈ BroadcastIn (xs.extract 0 M))
    (hb₂ : b₂ ∈ BroadcastIn (xs.extract 0 M))
    (hprec : CausalPrec (xs.extract 0 M) b₁ b₂) :
    CausalPrec (xs.extract 0 N) b₁ b₂ :=
  (bss_causalPrec_iff_ts_lt (omega_mTr_prefix hinit he N) (broadcastIn_extract_mono xs hMN hb₁)
    (broadcastIn_extract_mono xs hMN hb₂)).mpr
    ((bss_causalPrec_iff_ts_lt (omega_mTr_prefix hinit he M) hb₁ hb₂).mp hprec)

/-- A packet emitted by one step carries its sender's incremented clock and is delivered locally
by that step. -/
private theorem emittedPacket_spec {s : BSSState P V} {act : BSSAction P V} {b : Packet P V}
    (h : emittedPacket s act = some b) :
    b.ts = bssNextTimestamp (s.proc b.sender).vt b.sender ∧
      b ∈ ((bssStep s act).proc b.sender).delivered := by
  cases act <;> simp only [emittedPacket, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [bssBroadcastPacket, bssStep, bssExecBroadcast, bssExecCrashBroadcast]

/-! ### Liveness under packet transmission and atomic multicast -/

/-- Single-group single-hop `CBCAST` liveness step under causal-ancestor packet transmission (toward
#7297, after [BirmanSchiperStephenson1991], §5.1, Liveness, p. 283): for any crash-fault set
`F : Set P` (without any quorum or majority bound), in any fair infinite execution `(ss, xs)`
starting from `bssInit P V`, if `q ∉ F` and `b` (along with every causal predecessor `b' ≺_bcast b`)
was transmitted to `q` (`PacketSentTo q ss xs`), then `q` eventually delivers `b`.

Proved by strong induction on total vector-timestamp weight `vtWeight b.ts = ∑ r, b.ts r`. -/
theorem bss_live_of_packetSentTo {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)}
    (hinit : ss 0 = bssInit P V) (he : (bssLTS F).OmegaExecution ss xs)
    (hfair : BSSFair F ss xs) {q : P} (hq : q ∉ F) {b : Packet P V}
    (hsent_b : PacketSentTo q ss xs b)
    (hsent_pred : ∀ b', OmegaCausalPrec ss xs b' b → PacketSentTo q ss xs b') :
    ∃ k, b ∈ ((ss k).proc q).delivered := by
  obtain ⟨w, hw⟩ : ∃ w, vtWeight b.ts = w := ⟨_, rfl⟩
  induction w using Nat.strongRecOn generalizing b with
  | ind w ih =>
  obtain ⟨k₀, hem_b, hdest_b⟩ := hsent_b
  have hb_in := emittedPacket_mem_broadcastIn hinit he hem_b
  obtain ⟨hb_ts, hb_del⟩ := emittedPacket_spec hem_b
  obtain ⟨_, hstep₀⟩ := he k₀
  rcases hdest_b with hself | hinFlight
  · -- Case 1: `q = b.sender`; `q` delivered `b` locally immediately at step `k₀ + 1`.
    exact ⟨k₀ + 1, by rw [hstep₀, ← hself]; exact hb_del⟩
  -- Case 2: `⟨q, b⟩ ∈ (ss (k₀ + 1)).inFlight`. By induction, `q` eventually delivers every packet
  -- that `b.sender` had delivered before broadcasting `b`.
  obtain ⟨k₁, hk₁_ge, hrecv⟩ := hfair.fair_recv ⟨q, b⟩ hq (k₀ + 1) hinFlight
  have hb_pend : b ∈ ((ss (k₁ + 1)).proc q).pending := by
    obtain ⟨_, hstep⟩ := he k₁
    rw [hstep, hrecv]
    simp [bssStep, bssExecRecv]
  have hinv₀ := bssInv_of_mTr (omega_mTr_prefix hinit he k₀)
  have hcoord : ∀ r, ∃ kr, ((ss k₀).proc b.sender).vt r ≤ ((ss kr).proc q).vt r := by
    intro r
    rcases Nat.eq_zero_or_pos (((ss k₀).proc b.sender).vt r) with h0 | h1
    · exact ⟨0, by omega⟩
    obtain ⟨b_r, hb_r_del, rfl, hb_r_ts⟩ := hinv₀.exists_delivered_of_le_vt b.sender r _ h1 le_rfl
    have hb_r_in := broadcastIn_extract_mono xs (Nat.le_succ k₀)
      (hinv₀.delivered_mem b.sender b_r hb_r_del)
    have hb_r_lt : b_r.ts < b.ts := lt_of_le_of_lt (hinv₀.ts_le_vt b.sender b_r hb_r_del)
      (hb_ts ▸ lt_update_self_iff.mpr (Nat.lt_succ_self _))
    have hprec_r :=
      (bss_causalPrec_iff_ts_lt (omega_mTr_prefix hinit he (k₀ + 1)) hb_r_in hb_in).mpr hb_r_lt
    obtain ⟨kr, hkr⟩ := ih (vtWeight b_r.ts) (hw ▸ vtWeight_strictMono hb_r_lt)
      (hsent_pred b_r ⟨k₀ + 1, hb_r_in, hb_in, hprec_r⟩)
      (fun b'' ⟨M, hb''_M, hb_r_M, hprec''⟩ => hsent_pred b'' ⟨max M (k₀ + 1),
        broadcastIn_extract_mono xs (le_max_left _ _) hb''_M,
        broadcastIn_extract_mono xs (le_max_right _ _) hb_in,
        (causalPrec_extract_mono hinit he (le_max_left _ _) hb''_M hb_r_M hprec'').trans
          (causalPrec_extract_mono hinit he (le_max_right _ _) hb_r_in hb_in hprec_r)⟩) rfl
    exact ⟨kr, hb_r_ts.symm.trans_le
      ((bssInv_of_mTr (omega_mTr_prefix hinit he kr)).ts_le_vt q b_r hkr b_r.sender)⟩
  choose krFn hkrFn using hcoord
  let K := max (k₁ + 1) (Finset.univ.sup krFn)
  have hk₁_le_K : k₁ + 1 ≤ K := le_max_left _ _
  by_cases hdel_K : b ∈ ((ss K).proc q).delivered
  · exact ⟨K, hdel_K⟩
  have hvt (r : P) : ((ss k₀).proc b.sender).vt r ≤ ((ss K).proc q).vt r :=
    (hkrFn r).trans (omega_vt_mono he
      ((Finset.le_sup (f := krFn) (Finset.mem_univ r)).trans (le_max_right _ _)) q r)
  have hlt := vt_sender_lt_of_not_delivered hinit he
    (broadcastIn_extract_mono xs (by omega) hb_in) hdel_K
  refine (hfair.fair_deliver q hq b K (omega_pending_persist he hk₁_le_K hb_pend hdel_K)
    ⟨?_, fun r hr => ?_⟩).imp fun _ h => h.2
  · have := hvt b.sender
    rw [hb_ts, bssNextTimestamp, Function.update_self] at hlt ⊢
    omega
  · rw [hb_ts, bssNextTimestamp, Function.update_of_ne hr]
    exact hvt r

/-- Predicate stating that an action is not a mid-multicast partial crash (`crashBroadcast`). -/
@[expose]
def IsAtomicMulticastAction {P V : Type*} : BSSAction P V → Prop
  | .crashBroadcast _ _ _ => False
  | _ => True

/-- Single-group `CBCAST` liveness step under atomic multicast steps without mid-send crashes
(toward #7297, after [BirmanSchiperStephenson1991], §5.1, p. 283): in any fair execution where
`IsAtomicMulticastAction` holds at every step (no torn `crashBroadcast`), every broadcast packet `b`
is eventually delivered by every non-faulty process `q ∉ F`, for arbitrary `F : Set P`. -/
theorem bss_live_of_atomic_multicast {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)}
    (hinit : ss 0 = bssInit P V) (he : (bssLTS F).OmegaExecution ss xs)
    (hfair : BSSFair F ss xs) (hatomic : ∀ k, IsAtomicMulticastAction (xs k))
    {q : P} (hq : q ∉ F) {k₀ : ℕ} {b : Packet P V}
    (hem : emittedPacket (ss k₀) (xs k₀) = some b) :
    ∃ k, b ∈ ((ss k).proc q).delivered := by
  have hsent_all (k' : ℕ) (b' : Packet P V) (hem' : emittedPacket (ss k') (xs k') = some b') :
      PacketSentTo q ss xs b' := by
    refine ⟨k', hem', or_iff_not_imp_left.mpr fun hsq => ?_⟩
    obtain ⟨_, hstep⟩ := he k'
    have hat := hatomic k'
    rw [hstep]
    cases hact : xs k' <;> simp only [hact, emittedPacket, reduceCtorEq, Option.some.injEq,
      IsAtomicMulticastAction] at hem' hat
    subst hem'
    simp only [bssBroadcastPacket] at hsq
    simp [bssStep, bssExecBroadcast, Multiset.mem_erase_of_ne (Ne.symm hsq)]
  refine bss_live_of_packetSentTo hinit he hfair hq (hsent_all k₀ b hem) ?_
  rintro b' ⟨N, ⟨i, hi, hbi⟩, -⟩
  exact hsent_all i b' ((emittedPacket_extract hinit he hi).symm.trans hbi)

/-- Bundled single-group `CBCAST` safety and atomic-multicast liveness specification (toward #7297)
satisfied by `bssLTS F` for an arbitrary crash-fault set `F : Set P`: uniform integrity, duplicate
freedom, uniform causal delivery order, and fair liveness at `q ∉ F` under
`IsAtomicMulticastAction`. -/
@[expose]
def BSSSolvesAtomicMulticastCausalBroadcast (P V : Type*)
    [Fintype P] [DecidableEq P] [DecidableEq V] (F : Set P) : Prop :=
  (∀ xl s, (bssLTS (P := P) (V := V) F).MTr (bssInit P V) xl s →
    (∀ q pkt, pkt ∈ (s.proc q).delivered → pkt ∈ BroadcastIn xl) ∧
    (∀ q, (s.proc q).delivered.Nodup) ∧
    (∀ b₁ ∈ BroadcastIn xl, ∀ b₂ ∈ BroadcastIn xl, CausalPrec xl b₁ b₂ →
      ∀ q, b₂ ∈ (s.proc q).delivered →
        b₁ ∈ (s.proc q).delivered ∧
          (s.proc q).delivered.idxOf b₁ < (s.proc q).delivered.idxOf b₂)) ∧
  (∀ ss xs, ss 0 = bssInit P V → (bssLTS (P := P) (V := V) F).OmegaExecution ss xs →
    BSSFair F ss xs → (∀ k, IsAtomicMulticastAction (xs k)) →
    ∀ q ∉ F, ∀ k₀ b, emittedPacket (ss k₀) (xs k₀) = some b →
      ∃ k, b ∈ ((ss k).proc q).delivered)

/-- Single-group single-hop `CBCAST` safety and atomic-multicast liveness step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1): for every static crash-fault set `F : Set P` (without any
quorum or majority restriction), `bssLTS F` satisfies
`BSSSolvesAtomicMulticastCausalBroadcast P V F`. -/
theorem bss_solves_atomicMulticast_causalBroadcast (F : Set P) :
    BSSSolvesAtomicMulticastCausalBroadcast P V F :=
  ⟨fun _ _ hmtr =>
    ⟨bss_integrity hmtr,
     bss_no_duplicates hmtr,
     fun _ hb₁ _ hb₂ hprec q hd => bss_causal_delivery hmtr hb₁ hb₂ hprec q hd⟩,
   fun _ _ hinit he hfair hatomic _ hq _ _ hem =>
     bss_live_of_atomic_multicast hinit he hfair hatomic hq hem⟩

end Liveness

end Cslib.Distributed.CausalBroadcast
