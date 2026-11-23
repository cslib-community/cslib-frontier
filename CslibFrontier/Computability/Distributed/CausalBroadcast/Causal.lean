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
  simp only [Pi.sup_apply]
  by_cases hr : r = pkt.sender
  · subst hr
    rw [Function.update_self, h.1]
    exact Nat.max_eq_right (Nat.le_succ _)
  · rw [Function.update_of_ne hr]
    exact Nat.max_eq_left (h.2 r hr)

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
    constructor
    · intro h
      cases h
      exact ⟨trivial, rfl⟩
    · rintro ⟨_, rfl⟩
      exact LTS.MTr.refl
  | cons act xl ih =>
    constructor
    · intro h
      cases h with
      | stepL htr hmtr =>
        rcases htr with ⟨hen, rfl⟩
        obtain ⟨hv, hs⟩ := (ih (bssStep s₀ act)).mp hmtr
        exact ⟨⟨hen, hv⟩, hs⟩
    · rintro ⟨⟨hen, hv⟩, rfl⟩
      exact LTS.MTr.stepL ⟨hen, rfl⟩ ((ih (bssStep s₀ act)).mpr ⟨hv, rfl⟩)

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

private theorem broadcastIn_append_none {xl : List (BSSAction P V)} {act : BSSAction P V}
    (hnone : emittedPacket (bssRun (bssInit P V) xl) act = none) :
    BroadcastIn (xl ++ [act]) = BroadcastIn xl := by
  ext b
  simp only [BroadcastIn, Set.mem_ofPred, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨i, hi, hem⟩
    by_cases hlt : i < xl.length
    · rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hlt), List.getElem_append_left hlt] at hem
      exact ⟨i, hlt, hem⟩
    · have heq : i = xl.length := by omega
      subst heq
      rw [bssStateAt_append_of_le xl act (le_refl _), bssStateAt_length,
        List.getElem_append_right (le_refl _)] at hem
      simp only [Nat.sub_self, List.getElem_cons_zero] at hem
      rw [hnone] at hem
      cases hem
  · rintro ⟨i, hi, hem⟩
    refine ⟨i, by omega, ?_⟩
    rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hi), List.getElem_append_left hi]
    exact hem

private theorem broadcastIn_append_some {xl : List (BSSAction P V)} {act : BSSAction P V}
    {pkt : Packet P V} (hsome : emittedPacket (bssRun (bssInit P V) xl) act = some pkt) :
    BroadcastIn (xl ++ [act]) = insert pkt (BroadcastIn xl) := by
  ext b
  simp only [BroadcastIn, Set.mem_ofPred, Set.mem_insert_iff, List.length_append,
    List.length_singleton]
  constructor
  · rintro ⟨i, hi, hem⟩
    by_cases hlt : i < xl.length
    · right
      rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hlt), List.getElem_append_left hlt] at hem
      exact ⟨i, hlt, hem⟩
    · left
      have heq : i = xl.length := by omega
      subst heq
      rw [bssStateAt_append_of_le xl act (le_refl _), bssStateAt_length,
        List.getElem_append_right (le_refl _)] at hem
      simp only [Nat.sub_self, List.getElem_cons_zero] at hem
      rw [hsome] at hem
      exact (Option.some.inj hem).symm
  · rintro (rfl | ⟨i, hi, hem⟩)
    · refine ⟨xl.length, by omega, ?_⟩
      rw [bssStateAt_append_of_le xl act (le_refl _), bssStateAt_length,
        List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      exact hsome
    · refine ⟨i, by omega, ?_⟩
      rw [bssStateAt_append_of_le xl act (Nat.le_of_lt hi), List.getElem_append_left hi]
      exact hem

/-- One step of `bssStep` never decreases any coordinate of any process's vector clock. -/
private theorem bssStep_vt_le (s : BSSState P V) (act : BSSAction P V) (q : P) :
    (s.proc q).vt ≤ ((bssStep s act).proc q).vt := by
  cases act with
  | broadcast p _ | crashBroadcast p _ _ =>
    rcases eq_or_ne q p with rfl | hqp
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, Function.update_self,
        bssBroadcastPacket, bssNextTimestamp]
      exact le_update_self_iff.mpr (Nat.le_succ _)
    · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, Function.update_of_ne hqp,
        le_rfl]
  | deliver p _ =>
    rcases eq_or_ne q p with rfl | hqp
    · simp only [bssStep, bssExecDeliver, Function.update_self]
      exact le_update_self_iff.mpr (Nat.le_succ _)
    · simp only [bssStep, bssExecDeliver, Function.update_of_ne hqp, le_rfl]
  | recv _ =>
    simp only [bssStep, bssExecRecv, Function.apply_update (fun _ => BSSProcState.vt),
      Function.update_eq_self, le_rfl]
  | crash _ =>
    simp only [bssStep, bssExecCrash, Function.apply_update (fun _ => BSSProcState.vt),
      Function.update_eq_self, le_rfl]
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
  | recv _ =>
    simp only [bssStep, bssExecRecv, Function.apply_update (fun _ => BSSProcState.delivered),
      Function.update_eq_self, List.prefix_refl]
  | crash _ =>
    simp only [bssStep, bssExecCrash, Function.apply_update (fun _ => BSSProcState.delivered),
      Function.update_eq_self, List.prefix_refl]
  | stutter => exact List.prefix_refl _

/-- Multi-step `delivered` prefix monotonicity along `bssRun`. -/
private theorem bssRun_delivered_prefix (s : BSSState P V) (xl : List (BSSAction P V)) (q : P) :
    (s.proc q).delivered <+: ((bssRun s xl).proc q).delivered := by
  induction xl generalizing s with
  | nil => exact List.prefix_refl _
  | cons act xl ih =>
    exact (bssStep_delivered_prefix s act q).trans (ih (bssStep s act))

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

private theorem bssAppendSingleton_at (xl : List (BSSAction P V)) (act : BSSAction P V)
    {i : ℕ} (hi : i < (xl ++ [act]).length) :
    (∃ hilt : i < xl.length,
      bssStateAt (xl ++ [act]) i = bssStateAt xl i ∧ (xl ++ [act])[i] = xl[i]) ∨
    (i = xl.length ∧
      bssStateAt (xl ++ [act]) i = bssRun (bssInit P V) xl ∧ (xl ++ [act])[i] = act) := by
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < xl.length
  · exact Or.inl ⟨hlt, bssStateAt_append_of_le xl act (Nat.le_of_lt hlt),
      List.getElem_append_left hlt⟩
  · have heq : i = xl.length := by omega
    subst heq
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · rw [bssStateAt_append_of_le xl act (le_refl _), bssStateAt_length]
    · simp [List.getElem_append_right (le_refl _)]

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
        have hs_eq : s = bssRun (bssStateAt xl i) (xl.drop i) := by
          rw [hs, bssStateAt]; conv_lhs => rw [← List.take_append_drop i xl, bssRun_append]
        exact hs_eq ▸ bssRun_vt_le (bssStateAt xl i) (xl.drop i) p
      have hb₁_le_s : b₁.ts ≤ (s.proc p).vt := fun r => by
        rcases eq_or_ne r b₁.sender with rfl | hr
        · exact hsend ▸ (hinv.bcast_sender_bounds b₁ hb₁_mem).2
        · rw [hb₁_spec, bssNextTimestamp, Function.update_of_ne hr, hsend]; exact hvt_mono r
      refine ⟨lt_of_le_of_lt hb₁_le_s hvt_lt_pkt, ?_⟩
      have hle_p : b₁.ts p ≤ (s.proc p).vt p := hb₁_le_s p
      have hpkt_p : pkt.sender = p := rfl
      rw [hsend, hpkt_p, hpkt_ts_p]; omega

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
    have hrun_step : bssRun (bssInit P V) (xl ++ [act]) = bssStep s act := by
      rw [bssRun_append, ← hs_def]
      rfl
    rw [hrun_step]
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

/-- Broadcast packets along a valid trace are uniquely determined by `(sender, ts sender)`. -/
private theorem eq_of_sender_eq_of_ts_sender_eq {F : Set P} {xl : List (BSSAction P V)}
    {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s)
    {b₁ b₂ : Packet P V} (hb₁ : b₁ ∈ BroadcastIn xl) (hb₂ : b₂ ∈ BroadcastIn xl)
    (hsend : b₁.sender = b₂.sender) (hts : b₁.ts b₁.sender = b₂.ts b₂.sender) :
    b₁ = b₂ := by
  obtain ⟨hv, _⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  have hinv := bssInv_of_validTrace hv
  obtain ⟨i, hi, hbi⟩ := hb₁
  obtain ⟨j, hj, hbj⟩ := hb₂
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact absurd hts (ne_of_lt (hinv.same_sender_lt i j hi hj b₁ b₂ hij hbi hbj hsend).2)
  · rw [hbi] at hbj
    exact Option.some.inj hbj
  · exact absurd hts.symm (ne_of_lt (hinv.same_sender_lt j i hj hi b₂ b₁ hji hbj hbi hsend.symm).2)

/-- Single-group single-hop `CBCAST` uniform-integrity step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1, p. 281 and [HadzilacosToueg1994], §3.1, p. 10 & §3.8, p. 14):
in any execution of `bssLTS F` (for arbitrary `F : Set P`), every packet delivered at any process
`q` (faulty or correct) was broadcast earlier in the trace by `pkt.sender`. -/
theorem bss_integrity {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s) (q : P) {pkt : Packet P V}
    (hdeliv : pkt ∈ (s.proc q).delivered) :
    pkt ∈ BroadcastIn xl := by
  obtain ⟨hv, rfl⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  exact (bssInv_of_validTrace hv).delivered_mem q pkt hdeliv

/-- Single-group single-hop `CBCAST` duplicate-freedom step (toward #7297, after
[BirmanSchiperStephenson1991], §5.1, p. 281 and [HadzilacosToueg1994], §3.1, p. 10 & §3.8, p. 14):
in any reachable state of `bssLTS F` (for arbitrary `F : Set P`), every process `q`'s delivery log
`(s.proc q).delivered` contains no duplicate packets. -/
theorem bss_no_duplicates {F : Set P} {xl : List (BSSAction P V)} {s : BSSState P V}
    (hmtr : (bssLTS F).MTr (bssInit P V) xl s) (q : P) :
    (s.proc q).delivered.Nodup := by
  obtain ⟨hv, rfl⟩ := (bssLTS_mTr_iff F (bssInit P V) xl s).mp hmtr
  exact (bssInv_of_validTrace hv).delivered_nodup q

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
  · have hinv_j := bssInv_of_validTrace (validTrace_take hv j)
    have hle : b₁.ts ≤ ((bssStateAt xl j).proc b₂.sender).vt :=
      hinv_j.ts_le_vt b₂.sender b₁ hdel
    have hc_spec := hinv.bcast_emitted_spec j hj b₂ hbj
    exact lt_of_le_of_lt hle (hc_spec ▸ lt_update_self_iff.mpr (Nat.lt_succ_self _))

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
  constructor
  · intro hprec
    clear hb₁ hb₂
    induction hprec with
    | single hstep => exact causalStep_ts_lt hv hstep
    | tail _ hstep ih => exact lt_trans ih (causalStep_ts_lt hv hstep)
  · intro hlt
    by_cases hsend : b₁.sender = b₂.sender
    · obtain ⟨i, hi, hbi⟩ := hb₁
      obtain ⟨j, hj, hbj⟩ := hb₂
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact Relation.TransGen.single (Or.inl ⟨i, j, hi, hj, hij, hbi, hbj, hsend⟩)
      · rw [hbi] at hbj
        cases Option.some.inj hbj
        exact absurd hlt (lt_irrefl _)
      · exact absurd hlt (lt_asymm (hinv.same_sender_lt j i hj hi b₂ b₁ hji hbj hbi hsend.symm).1)
    · obtain ⟨j, hj, hbj⟩ := hb₂
      have hb₂_spec := hinv.bcast_emitted_spec j hj b₂ hbj
      have hk1 : 1 ≤ b₁.ts b₁.sender := (hinv.bcast_sender_bounds b₁ hb₁).1
      have hkle : b₁.ts b₁.sender ≤ ((bssStateAt xl j).proc b₂.sender).vt b₁.sender := by
        have hle_coord : b₁.ts b₁.sender ≤ b₂.ts b₁.sender := (le_of_lt hlt) b₁.sender
        rwa [hb₂_spec, bssNextTimestamp, Function.update_of_ne hsend] at hle_coord
      have hinv_j := bssInv_of_validTrace (validTrace_take hv j)
      obtain ⟨b', hb'_del, hb'_send, hb'_ts⟩ :=
        hinv_j.exists_delivered_of_le_vt b₂.sender b₁.sender (b₁.ts b₁.sender) hk1 hkle
      have hb'_mem : b' ∈ BroadcastIn xl :=
        broadcastIn_take_subset xl j (hinv_j.delivered_mem b₂.sender b' hb'_del)
      have hb'_eq : b' = b₁ :=
        eq_of_sender_eq_of_ts_sender_eq hmtr hb'_mem hb₁ hb'_send (hb'_send.symm ▸ hb'_ts)
      subst hb'_eq
      exact Relation.TransGen.single (Or.inr ⟨hb₁, j, hj, hbj, hb'_del⟩)

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
    rw [hsend] at hlt_coord ⊢
    simp only [bssBroadcastPacket, bssNextTimestamp, Function.update_self] at hlt_coord
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
  have hk1 : 1 ≤ b₁.ts b₁.sender := (hinv.bcast_sender_bounds b₁ hb₁).1
  -- Consider the first prefix of `xl` after which `b₂ ∈ delivered` at `q`.
  have hex : ∃ m ≤ xl.length, b₂ ∈ ((bssStateAt xl m).proc q).delivered :=
    ⟨xl.length, le_refl _, by simpa [bssStateAt_length] using hdel₂⟩
  let m := Nat.find hex
  have hm_spec := Nat.find_spec hex
  have hm_le : m ≤ xl.length := hm_spec.1
  have hm_del₂ : b₂ ∈ ((bssStateAt xl m).proc q).delivered := hm_spec.2
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := by omega
    rw [hm_zero] at hm_del₂
    simp [bssStateAt, bssRun, bssInit] at hm_del₂
  let k := m - 1
  have hk_lt_m : k < m := by omega
  have hk_lt_len : k < xl.length := by omega
  have hnot_del₂_k : b₂ ∉ ((bssStateAt xl k).proc q).delivered := by
    intro hcontra
    exact Nat.find_min hex hk_lt_m ⟨by omega, hcontra⟩
  have htake_succ : xl.take m = xl.take k ++ [xl[k]] := by
    have hm_eq : m = k + 1 := by omega
    rw [hm_eq, List.take_add_one, List.getElem?_eq_getElem hk_lt_len, Option.toList_some]
  have hstate_m : bssStateAt xl m = bssStep (bssStateAt xl k) xl[k] := by
    simp only [bssStateAt, htake_succ, bssRun_append]
    rfl
  have hv_m : bssValidTrace F (bssInit P V) (xl.take m) := validTrace_take hv m
  rw [htake_succ] at hv_m
  obtain ⟨hv_k, hen_k⟩ := (bssValidTrace_append_iff F (bssInit P V) (xl.take k) xl[k]).mp hv_m
  have hinv_k := bssInv_of_validTrace hv_k
  -- Show `b₁` was already delivered in `bssStateAt xl k`!
  have hb₁_in_k : b₁ ∈ ((bssStateAt xl k).proc q).delivered := by
    suffices hkle : b₁.ts b₁.sender ≤ ((bssStateAt xl k).proc q).vt b₁.sender by
      obtain ⟨b', hb'_del, hb'_send, hb'_ts⟩ :=
        hinv_k.exists_delivered_of_le_vt q b₁.sender (b₁.ts b₁.sender) hk1 hkle
      have hb'_mem : b' ∈ BroadcastIn xl :=
        broadcastIn_take_subset xl k (hinv_k.delivered_mem q b' hb'_del)
      have hmtr_xl : (bssLTS F).MTr (bssInit P V) xl (bssRun (bssInit P V) xl) :=
        (bssLTS_mTr_iff F (bssInit P V) xl _).mpr ⟨hv, rfl⟩
      have hb'_eq : b' = b₁ :=
        eq_of_sender_eq_of_ts_sender_eq hmtr_xl hb'_mem hb₁ hb'_send (hb'_send.symm ▸ hb'_ts)
      rwa [← hb'_eq]
    -- Case-split on the action `xl[k]` that caused `b₂` to enter `delivered` at `q`.
    rw [hstate_m] at hm_del₂
    cases hp : xl[k] with
    | broadcast p payload | crashBroadcast p _ payload =>
      rw [hp] at hm_del₂
      rcases eq_or_ne p q with rfl | hpq
      · simp only [bssStep, bssExecBroadcast, bssExecCrashBroadcast, Function.update_self,
          List.mem_append, List.mem_singleton] at hm_del₂
        rcases hm_del₂ with hcontra | hb₂_eq
        · exact absurd hcontra hnot_del₂_k
        · rw [hb₂_eq] at hts_lt
          exact local_bcast_ts_le_vt hinv hk_lt_len hb₁ hts_lt (by simp [hp, emittedPacket])
      · exact (hnot_del₂_k (by
          simpa only [bssStep, bssExecBroadcast, bssExecCrashBroadcast,
            Function.update_of_ne hpq.symm] using hm_del₂)).elim
    | deliver p pkt =>
      rw [hp] at hm_del₂ hen_k
      rcases eq_or_ne p q with rfl | hpq
      · simp only [bssStep, bssExecDeliver, Function.update_self, List.mem_append,
          List.mem_singleton] at hm_del₂
        rcases hm_del₂ with hcontra | hb₂_eq
        · exact absurd hcontra hnot_del₂_k
        · rw [← hb₂_eq] at hen_k
          have hdeliv_guard : Deliverable ((bssStateAt xl k).proc p).vt b₂ := hen_k.2.2
          by_cases hsend : b₁.sender = b₂.sender
          · have hlt_coord := same_sender_coord_lt_of_ts_lt hinv hb₁ hb₂ hsend hts_lt
            rw [hsend, hdeliv_guard.1] at hlt_coord; rw [hsend]; omega
          · exact le_trans ((le_of_lt hts_lt) b₁.sender) (hdeliv_guard.2 b₁.sender hsend)
      · exact (hnot_del₂_k (by
          simpa only [bssStep, bssExecDeliver, Function.update_of_ne hpq.symm] using hm_del₂)).elim
    | recv _ =>
      rw [hp] at hm_del₂
      exact (hnot_del₂_k (by
        simpa only [bssStep, bssExecRecv, Function.apply_update (fun _ => BSSProcState.delivered),
          Function.update_eq_self] using hm_del₂)).elim
    | crash _ =>
      rw [hp] at hm_del₂
      exact (hnot_del₂_k (by
        simpa only [bssStep, bssExecCrash, Function.apply_update (fun _ => BSSProcState.delivered),
          Function.update_eq_self] using hm_del₂)).elim
    | stutter => rw [hp] at hm_del₂; exact absurd hm_del₂ hnot_del₂_k
  -- Now `b₁ ∈ delivered` at step `k`, while `b₂` is appended at step `m = k + 1`!
  have hpref_k_m : ((bssStateAt xl k).proc q).delivered <+:
      ((bssStateAt xl m).proc q).delivered := by
    rw [hstate_m]
    exact bssStep_delivered_prefix (bssStateAt xl k) xl[k] q
  have hpref_m_end : ((bssStateAt xl m).proc q).delivered <+:
      ((bssRun (bssInit P V) xl).proc q).delivered := by
    have hsplit : xl = xl.take m ++ xl.drop m := (List.take_append_drop m xl).symm
    conv_rhs => rw [hsplit, bssRun_append]
    exact bssRun_delivered_prefix (bssStateAt xl m) (xl.drop m) q
  have hpref_k_end := hpref_k_m.trans hpref_m_end
  have hb₁_end : b₁ ∈ ((bssRun (bssInit P V) xl).proc q).delivered :=
    hpref_k_end.subset hb₁_in_k
  refine ⟨hb₁_end, ?_⟩
  set l_k := ((bssStateAt xl k).proc q).delivered
  set l_end := ((bssRun (bssInit P V) xl).proc q).delivered
  obtain ⟨tail, hl_eq⟩ := hpref_k_end
  have hidx₁_lt : l_k.idxOf b₁ < l_k.length := List.idxOf_lt_length_of_mem hb₁_in_k
  have hidx₁_eq : l_end.idxOf b₁ = l_k.idxOf b₁ := by
    rw [← hl_eq, List.idxOf_append_of_mem hb₁_in_k]
  have hidx₂_ge : l_k.length ≤ l_end.idxOf b₂ := by
    rw [← hl_eq, List.idxOf_append_of_notMem hnot_del₂_k]
    omega
  omega

end Invariants

section Liveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

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
  have hmtr := he.extract_mTr hij
  obtain ⟨_, hrun⟩ := (bssLTS_mTr_iff F (ss i) (xs.extract i j) (ss j)).mp hmtr
  rw [hrun]
  exact bssRun_vt_le (ss i) (xs.extract i j) q

/-- Monotonicity of `delivered` along an `OmegaExecution` of `bssLTS F`: once `pkt` has been
delivered at `q` at step `i`, it remains in `((ss j).proc q).delivered` at every step `j ≥ i`. -/
theorem bss_omega_delivered_mono {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (he : (bssLTS F).OmegaExecution ss xs)
    {i j : ℕ} (hij : i ≤ j) {q : P} {pkt : Packet P V}
    (h : pkt ∈ ((ss i).proc q).delivered) :
    pkt ∈ ((ss j).proc q).delivered := by
  have hmtr := he.extract_mTr hij
  obtain ⟨_, hrun⟩ := (bssLTS_mTr_iff F (ss i) (xs.extract i j) (ss j)).mp hmtr
  rw [hrun]
  exact (bssRun_delivered_prefix (ss i) (xs.extract i j) q).subset h

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
    cases hact : xs (k + d) with
    | broadcast _ _ =>
      simpa only [bssStep, bssExecBroadcast, Function.apply_update (fun _ => BSSProcState.pending),
        Function.update_eq_self] using hpend_d
    | crashBroadcast _ _ _ =>
      simpa only [bssStep, bssExecCrashBroadcast,
        Function.apply_update (fun _ => BSSProcState.pending), Function.update_eq_self]
        using hpend_d
    | recv m =>
      rcases eq_or_ne q m.dest with rfl | hqm
      · simp only [bssStep, bssExecRecv, Function.update_self]
        exact Multiset.mem_cons_of_mem hpend_d
      · simpa only [bssStep, bssExecRecv, Function.update_of_ne hqm] using hpend_d
    | deliver p pkt' =>
      rw [hact] at hnot_del
      rcases eq_or_ne q p with rfl | hqp
      · simp only [bssStep, bssExecDeliver, Function.update_self, List.mem_append,
          List.mem_singleton] at hnot_del ⊢
        exact (Multiset.mem_erase_of_ne fun heq => hnot_del (Or.inr heq)).mpr hpend_d
      · simpa only [bssStep, bssExecDeliver, Function.update_of_ne hqp] using hpend_d
    | crash _ =>
      simpa only [bssStep, bssExecCrash, Function.apply_update (fun _ => BSSProcState.pending),
        Function.update_eq_self] using hpend_d
    | stutter => exact hpend_d

private theorem vt_sender_lt_of_not_delivered {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {j : ℕ} {q : P} {pkt : Packet P V}
    (hpkt_in : pkt ∈ BroadcastIn (xs.extract 0 j))
    (hnot_del : pkt ∉ ((ss j).proc q).delivered) :
    ((ss j).proc q).vt pkt.sender < pkt.ts pkt.sender := by
  by_contra hge_neg
  have hgt : pkt.ts pkt.sender ≤ ((ss j).proc q).vt pkt.sender := by omega
  have hmtr_j := omega_mTr_prefix hinit he j
  obtain ⟨hv_j, hrun_j⟩ := (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 j) (ss j)).mp hmtr_j
  have hinv_j := bssInv_of_validTrace hv_j
  have hk1 : 1 ≤ pkt.ts pkt.sender := (hinv_j.bcast_sender_bounds pkt hpkt_in).1
  rw [hrun_j] at hgt
  obtain ⟨b', hb'_del, hb'_send, hb'_ts⟩ :=
    hinv_j.exists_delivered_of_le_vt q pkt.sender (pkt.ts pkt.sender) hk1 hgt
  have hb'_bcast : b' ∈ BroadcastIn (xs.extract 0 j) := hinv_j.delivered_mem q b' hb'_del
  have hmtr_run : (bssLTS F).MTr (bssInit P V) (xs.extract 0 j)
      (bssRun (bssInit P V) (xs.extract 0 j)) :=
    (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 j) _).mpr ⟨hv_j, rfl⟩
  have hb'_eq : b' = pkt :=
    eq_of_sender_eq_of_ts_sender_eq hmtr_run hb'_bcast hpkt_in hb'_send
      (hb'_send.symm ▸ hb'_ts)
  rw [hb'_eq, ← hrun_j] at hb'_del
  exact hnot_del hb'_del

/-- Once a buffered packet `pkt` at `q` satisfies `Deliverable` at step `k`, it remains buffered
and `Deliverable` at every subsequent step `j ≥ k` until `q` delivers `pkt`. -/
theorem deliverable_stable_until_delivered {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {q : P} {pkt : Packet P V} {k j : ℕ} (hkj : k ≤ j)
    (hpend : pkt ∈ ((ss k).proc q).pending) (hdeliv : Deliverable ((ss k).proc q).vt pkt)
    (hnot_del : pkt ∉ ((ss j).proc q).delivered) :
    pkt ∈ ((ss j).proc q).pending ∧ Deliverable ((ss j).proc q).vt pkt := by
  have hpend_j := omega_pending_persist he hkj hpend hnot_del
  refine ⟨hpend_j, ?_⟩
  have hvt_le := omega_vt_mono he hkj q
  refine ⟨?_, fun r hr => le_trans (hdeliv.2 r hr) (hvt_le r)⟩
  have hle_low : ((ss k).proc q).vt pkt.sender ≤ ((ss j).proc q).vt pkt.sender :=
    hvt_le pkt.sender
  have hmtr_j := omega_mTr_prefix hinit he j
  obtain ⟨hv_j, hrun_j⟩ := (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 j) (ss j)).mp hmtr_j
  have hpkt_bcast : pkt ∈ BroadcastIn (xs.extract 0 j) := by
    rw [hrun_j] at hpend_j
    exact ((bssInv_of_validTrace hv_j).pending_wf q pkt hpend_j).1
  have hlt := vt_sender_lt_of_not_delivered hinit he hpkt_bcast hnot_del
  have h1 := hdeliv.1
  omega

private theorem broadcastIn_extract_mono (xs : ωSequence (BSSAction P V)) {M N : ℕ}
    (hMN : M ≤ N) :
    BroadcastIn (xs.extract 0 M : List (BSSAction P V)) ⊆
      BroadcastIn (xs.extract 0 N : List (BSSAction P V)) :=
  extract_take_eq xs hMN ▸ broadcastIn_take_subset (xs.extract 0 N) M

private theorem emittedPacket_mem_broadcastIn {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {k : ℕ} {b : Packet P V}
    (hem : emittedPacket (ss k) (xs k) = some b) :
    b ∈ BroadcastIn (xs.extract 0 (k + 1)) := by
  have hlen : k < (xs.extract 0 (k + 1)).length := by
    simp [ωSequence.length_extract]
  refine ⟨k, hlen, ?_⟩
  have hmtr_k := omega_mTr_prefix hinit he k
  obtain ⟨_, hrun_k⟩ := (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 k) (ss k)).mp hmtr_k
  have htake : (xs.extract 0 (k + 1)).take k = xs.extract 0 k :=
    extract_take_eq xs (Nat.le_succ k)
  have hget : (xs.extract 0 (k + 1))[k] = xs k := by
    rw [ωSequence.get_extract (by omega), Nat.zero_add]
  simp [bssStateAt, htake, ← hrun_k, hget, hem]

private theorem causalPrec_extract_mono {F : Set P} {ss : ωSequence (BSSState P V)}
    {xs : ωSequence (BSSAction P V)} (hinit : ss 0 = bssInit P V)
    (he : (bssLTS F).OmegaExecution ss xs) {M N : ℕ} (hMN : M ≤ N)
    {b₁ b₂ : Packet P V}
    (hb₁ : b₁ ∈ BroadcastIn (xs.extract 0 M))
    (hb₂ : b₂ ∈ BroadcastIn (xs.extract 0 M))
    (hprec : CausalPrec (xs.extract 0 M) b₁ b₂) :
    CausalPrec (xs.extract 0 N) b₁ b₂ := by
  have hmtrM := omega_mTr_prefix hinit he M
  have hmtrN := omega_mTr_prefix hinit he N
  have hlt := (bss_causalPrec_iff_ts_lt hmtrM hb₁ hb₂).mp hprec
  exact (bss_causalPrec_iff_ts_lt hmtrN
    (broadcastIn_extract_mono xs hMN hb₁)
    (broadcastIn_extract_mono xs hMN hb₂)).mpr hlt

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
  suffices hmain : ∀ w : ℕ, ∀ b : Packet P V, vtWeight b.ts = w →
      PacketSentTo q ss xs b →
      (∀ b', OmegaCausalPrec ss xs b' b → PacketSentTo q ss xs b') →
      ∃ k, b ∈ ((ss k).proc q).delivered from
    hmain (vtWeight b.ts) b rfl hsent_b hsent_pred
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro b hw hsb hspred
    obtain ⟨k₀, hem_b, hdest_b⟩ := hsb
    have hb_in : b ∈ BroadcastIn (xs.extract 0 (k₀ + 1)) :=
      emittedPacket_mem_broadcastIn hinit he hem_b
    rcases hdest_b with hself | hinFlight
    · -- Case 1: `q = b.sender`; `q` delivered `b` locally immediately at step `k₀ + 1`.
      refine ⟨k₀ + 1, ?_⟩
      obtain ⟨_, hstep⟩ := he k₀
      rw [hstep]
      cases hact : xs k₀ with
      | broadcast p payload =>
        rw [hact] at hem_b
        simp only [emittedPacket, Option.some.injEq] at hem_b
        have hpq : p = q := by rw [← hself, ← hem_b]; rfl
        subst hpq hem_b
        simp [bssStep, bssExecBroadcast]
      | crashBroadcast p dests payload =>
        rw [hact] at hem_b
        simp only [emittedPacket, Option.some.injEq] at hem_b
        have hpq : p = q := by rw [← hself, ← hem_b]; rfl
        subst hpq hem_b
        simp [bssStep, bssExecCrashBroadcast]
      | recv _ | deliver _ _ | crash _ | stutter =>
        rw [hact] at hem_b; simp [emittedPacket] at hem_b
    · -- Case 2: `b.sender ≠ q` and `⟨q, b⟩ ∈ (ss (k₀ + 1)).inFlight`.
      obtain ⟨k₁, hk₁_ge, hrecv⟩ := hfair.fair_recv ⟨q, b⟩ hq (k₀ + 1) hinFlight
      have hb_pend : b ∈ ((ss (k₁ + 1)).proc q).pending := by
        obtain ⟨_, hstep⟩ := he k₁
        rw [hstep, hrecv]
        simp [bssStep, bssExecRecv]
      have hcoord : ∀ r : P, ∃ kr,
          (if r = b.sender then b.ts b.sender - 1 else b.ts r) ≤ ((ss kr).proc q).vt r := by
        intro r
        set target := if r = b.sender then b.ts b.sender - 1 else b.ts r
        by_cases ht0 : target = 0
        · exact ⟨0, by omega⟩
        · have ht1 : 1 ≤ target := by omega
          have hmtr_k₀ := omega_mTr_prefix hinit he k₀
          obtain ⟨hv_k₀, hrun_k₀⟩ :=
            (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 k₀) (ss k₀)).mp hmtr_k₀
          have hinv_k₀ := bssInv_of_validTrace hv_k₀
          have hb_ts_eq : b.ts = bssNextTimestamp ((ss k₀).proc b.sender).vt b.sender := by
            cases hact : xs k₀ with
            | broadcast p payload =>
              rw [hact] at hem_b
              cases Option.some.inj hem_b
              rfl
            | crashBroadcast p dests payload =>
              rw [hact] at hem_b
              cases Option.some.inj hem_b
              rfl
            | recv _ | deliver _ _ | crash _ | stutter =>
              rw [hact] at hem_b; simp [emittedPacket] at hem_b
          have htarget_le_vt : target ≤ ((ss k₀).proc b.sender).vt r := by
            simp only [target]
            by_cases hrs : r = b.sender
            · subst hrs
              simp only [↓reduceIte, hb_ts_eq, bssNextTimestamp, Function.update_self]
              omega
            · simp only [hrs, ↓reduceIte, hb_ts_eq, bssNextTimestamp, Function.update_of_ne hrs]
              exact le_rfl
          rw [hrun_k₀] at htarget_le_vt
          obtain ⟨b_r, hb_r_del, hb_r_send, hb_r_ts⟩ :=
            hinv_k₀.exists_delivered_of_le_vt b.sender r target ht1 htarget_le_vt
          have hb_r_in_k₀ : b_r ∈ BroadcastIn (xs.extract 0 k₀) :=
            hinv_k₀.delivered_mem b.sender b_r hb_r_del
          have hb_r_in : b_r ∈ BroadcastIn (xs.extract 0 (k₀ + 1)) :=
            broadcastIn_extract_mono xs (Nat.le_succ k₀) hb_r_in_k₀
          have hb_r_lt_b : b_r.ts < b.ts := by
            have hle_s : b_r.ts ≤ ((ss k₀).proc b.sender).vt :=
              hrun_k₀ ▸ hinv_k₀.ts_le_vt b.sender b_r hb_r_del
            exact lt_of_le_of_lt hle_s (hb_ts_eq ▸ lt_update_self_iff.mpr (Nat.lt_succ_self _))
          have hmtr_k₀1 := omega_mTr_prefix hinit he (k₀ + 1)
          have hprec_r : CausalPrec (xs.extract 0 (k₀ + 1)) b_r b :=
            (bss_causalPrec_iff_ts_lt hmtr_k₀1 hb_r_in hb_in).mpr hb_r_lt_b
          have hoprec_r : OmegaCausalPrec ss xs b_r b :=
            ⟨k₀ + 1, hb_r_in, hb_in, hprec_r⟩
          have hw_lt : vtWeight b_r.ts < w := hw ▸ vtWeight_strictMono hb_r_lt_b
          have hsent_b_r : PacketSentTo q ss xs b_r := hspred b_r hoprec_r
          have hsent_pred_r : ∀ b'', OmegaCausalPrec ss xs b'' b_r →
              PacketSentTo q ss xs b'' := by
            intro b'' ⟨M, hb''_M, hb_r_M, hprec''⟩
            let K := max M (k₀ + 1)
            have hprec''_K :=
              causalPrec_extract_mono hinit he (Nat.le_max_left M (k₀ + 1)) hb''_M hb_r_M hprec''
            have hprec_r_K :=
              causalPrec_extract_mono hinit he (Nat.le_max_right M (k₀ + 1)) hb_r_in hb_in hprec_r
            exact hspred b'' ⟨K,
              broadcastIn_extract_mono xs (Nat.le_max_left M (k₀ + 1)) hb''_M,
              broadcastIn_extract_mono xs (Nat.le_max_right M (k₀ + 1)) hb_in,
              hprec''_K.trans hprec_r_K⟩
          obtain ⟨kr, hkr_del⟩ := ih (vtWeight b_r.ts) hw_lt b_r rfl hsent_b_r hsent_pred_r
          refine ⟨kr, ?_⟩
          have hmtr_kr := omega_mTr_prefix hinit he kr
          obtain ⟨hv_kr, hrun_kr⟩ :=
            (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 kr) (ss kr)).mp hmtr_kr
          rw [hrun_kr] at hkr_del ⊢
          have hle_kr := (bssInv_of_validTrace hv_kr).ts_le_vt q b_r hkr_del r
          change target ≤ ((bssRun (bssInit P V) (xs.extract 0 kr)).proc q).vt r
          rw [← hb_r_ts]
          exact hle_kr
      choose krFn hkrFn using hcoord
      let K := max (k₁ + 1) (Finset.univ.sup krFn)
      by_cases hdel_K : b ∈ ((ss K).proc q).delivered
      · exact ⟨K, hdel_K⟩
      · have hk₁_le_K : k₁ + 1 ≤ K := Nat.le_max_left _ _
        have hpend_K : b ∈ ((ss K).proc q).pending :=
          omega_pending_persist he hk₁_le_K hb_pend hdel_K
        have hdeliv_K : Deliverable ((ss K).proc q).vt b := by
          have hall : ∀ r : P,
              (if r = b.sender then b.ts b.sender - 1 else b.ts r) ≤ ((ss K).proc q).vt r := by
            intro r
            have hr_le : krFn r ≤ K :=
              le_trans (Finset.le_sup (f := krFn) (Finset.mem_univ r)) (Nat.le_max_right _ _)
            exact le_trans (hkrFn r) (omega_vt_mono he hr_le q r)
          refine ⟨?_, fun r hr => ?_⟩
          · have hlow := hall b.sender
            simp only [↓reduceIte] at hlow
            have hb_in_K : b ∈ BroadcastIn (xs.extract 0 K) :=
              broadcastIn_extract_mono xs (by omega) hb_in
            have hlt := vt_sender_lt_of_not_delivered hinit he hb_in_K hdel_K
            omega
          · have hr_le := hall r
            simpa [hr] using hr_le
        obtain ⟨j, _, hj_del⟩ := hfair.fair_deliver q hq b K hpend_K hdeliv_K
        exact ⟨j, hj_del⟩

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
  have hsent_all : ∀ k' b', emittedPacket (ss k') (xs k') = some b' →
      PacketSentTo q ss xs b' := by
    intro k' b' hem'
    refine ⟨k', hem', ?_⟩
    by_cases hsq : b'.sender = q
    · exact Or.inl hsq
    · right
      obtain ⟨_, hstep⟩ := he k'
      rw [hstep]
      cases hact : xs k' with
      | broadcast p payload =>
        rw [hact] at hem'
        simp only [emittedPacket, Option.some.injEq] at hem'
        subst hem'
        simp only [bssStep, bssExecBroadcast, Multiset.mem_add, Multiset.mem_map]
        right
        exact ⟨q, Finset.mem_def.mp (Finset.mem_erase.mpr ⟨Ne.symm hsq, Finset.mem_univ q⟩), rfl⟩
      | crashBroadcast p dests payload =>
        have hfalse := hatomic k'
        rw [hact] at hfalse
        cases hfalse
      | recv _ | deliver _ _ | crash _ | stutter =>
        rw [hact] at hem'; simp [emittedPacket] at hem'
  refine bss_live_of_packetSentTo hinit he hfair hq (hsent_all k₀ b hem) ?_
  intro b' ⟨N, ⟨i, hi, hbi⟩, _, _⟩
  have hiN : i < N := by simp only [ωSequence.length_extract, Nat.sub_zero] at hi; exact hi
  have hmtr_i := omega_mTr_prefix hinit he i
  obtain ⟨_, hrun_i⟩ := (bssLTS_mTr_iff F (bssInit P V) (xs.extract 0 i) (ss i)).mp hmtr_i
  have htake : (xs.extract 0 N).take i = xs.extract 0 i :=
    extract_take_eq xs (Nat.le_of_lt hiN)
  have hget : (xs.extract 0 N)[i] = xs i := by
    rw [ωSequence.get_extract (by omega), Nat.zero_add]
  have hem_i : emittedPacket (ss i) (xs i) = some b' := by
    simpa [bssStateAt, htake, ← hrun_i, hget] using hbi
  exact hsent_all i b' hem_i

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
