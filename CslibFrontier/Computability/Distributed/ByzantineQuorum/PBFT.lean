/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ByzantineQuorum.QuorumSystems
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Function.Basic

/-!
# Practical Byzantine Fault Tolerance: Normal-Case and View-Change Multi-Slot SMR Step

This module formalizes an **ideal-authentication, checkpoint-free intermediate step** toward the
Practical Byzantine Fault Tolerance (`PBFT`) state-machine replication protocol of
[Castro and Liskov][CastroLiskov1999] (§§4.2, 4.4, 4.5, pp. 3–7; extended journal version
[CastroLiskov2002]), and **not** the full cryptographic, garbage-collected protocol of those papers,
as part of `#7506` (`#3261`).

## Model scope and explicit abstractions

Over a finite replica universe `P`, static Byzantine fault set `F : Finset P` (`F.card ≤ f`), view
numbers `v : ℕ` with primary schedule `primary : ℕ → P`, sequence slots `s : ℕ`, and request values
`V` (`Option V` carries `some val` for client requests and `none` for PBFT's `null` no-op request of
§4.4, p. 6):

* **General `3 * f < |P|` quorum threshold (`pbftQuorumSize P f = Fintype.card P - f`):**
  [CastroLiskov1999] §4 assumes `|P| = 3 * f + 1` for simplicity, where `2 * f + 1 = |P| - f`. Here
  certificates (`PreparedCert`, `CommittedLocal`, `NewView`) use quorum size `|P| - f`, which
  equals `2 * f + 1` when `|P| = 3 * f + 1` and forms an `f`-threshold dissemination quorum system
  for **every** `3 * f < Fintype.card P` via
  `isThresholdDisseminationQuorumSystem_thresholdQuorums_sub`.
* **Ideal sender signatures without digests or MAC vectors:** messages in `st.network` carry ideal
  unforgeable signer identity (`PBFTMsg.signer`); faulty replicas `j ∈ F` may inject arbitrary
  messages signed by `j ∈ F` (`PBFTAction.byzSend`), while messages signed by `i ∉ F` originate
  solely from honest replica transitions. Collision-resistant digests `D(m)` and §5.2 symmetric MAC
  authenticator vectors remain open under `#7506`.
* **Unbounded log (`min-s = 0` without checkpoint truncation):** replicas retain their accepted
  proposals and prepared certificates across views without §4.3 periodic `CHECKPOINT` garbage
  collection or `[h, H]` sequence-number watermarks, which remain open under `#7506` alongside
  §4.5.2 real-time exponential-backoff view-change timers and [CastroLiskov2002] proactive recovery.

## Main definitions

* `Cslib.Distributed.ByzantineQuorum.pbftQuorumSize`: Byzantine quorum threshold `|P| - f`.
* `Cslib.Distributed.ByzantineQuorum.SlotEntry`: `(view, slot, val)` record for accepted proposals
  and local commits.
* `Cslib.Distributed.ByzantineQuorum.PreparedCert`,
  `Cslib.Distributed.ByzantineQuorum.PreparedCert.voters`,
  `Cslib.Distributed.ByzantineQuorum.PreparedCert.ValidIn`: PBFT prepared certificate (`PrePrepare`
  from `primary view` plus matching backup `Prepare`s reaching `pbftQuorumSize P f`).
* `Cslib.Distributed.ByzantineQuorum.ViewChangeMsg`,
  `Cslib.Distributed.ByzantineQuorum.SlotProposal`,
  `Cslib.Distributed.ByzantineQuorum.PBFTMsg`,
  `Cslib.Distributed.ByzantineQuorum.PBFTMsg.signer`: PBFT protocol messages (`prePrepare`,
  `prepare`, `commit`, `viewChange`, `newView`) and their authenticated signers.
* `Cslib.Distributed.ByzantineQuorum.computeSlotVal`,
  `Cslib.Distributed.ByzantineQuorum.computeOset`,
  `Cslib.Distributed.ByzantineQuorum.ViewChangeMsg.ValidIn`,
  `Cslib.Distributed.ByzantineQuorum.NewViewValidIn`: deterministic `NEW-VIEW` `Oset` selection
  (highest-view prepared value per slot up to `max-s`, or `none`/`null` if unprepared) and validity
  predicates.
* `Cslib.Distributed.ByzantineQuorum.ReplicaState`,
  `Cslib.Distributed.ByzantineQuorum.PBFTState`,
  `Cslib.Distributed.ByzantineQuorum.PBFTAction`,
  `Cslib.Distributed.ByzantineQuorum.initPBFTState`,
  `Cslib.Distributed.ByzantineQuorum.pbftStep`,
  `Cslib.Distributed.ByzantineQuorum.PBFTReachable`: ghost-free replica state, asynchronous
  transition function, and reachable global configurations.
* `Cslib.Distributed.ByzantineQuorum.CommittedLocal`: honest-replica local commit predicate at
  `(view, slot, val)`.
* `Cslib.Distributed.ByzantineQuorum.executeSlotLog`: sequential deterministic state-machine
  execution over committed slot entries `0, ..., k - 1`.

## Main results

* `Cslib.Distributed.ByzantineQuorum.preparedCert_unique_idealAuth`: within-view non-equivocation
  step (after [CastroLiskov1999], §4.2, p. 4)—under `3 * f < Fintype.card P` and `F.card ≤ f`, any
  two valid `PreparedCert`s in a reachable state with the same `view` and `slot` have equal `val`.
* `Cslib.Distributed.ByzantineQuorum.committedLocal_preserves_higher_prepared_idealAuth`:
  cross-view commit-preservation step (after [CastroLiskov1999], §4.5.1, pp. 6–7)—if any honest
  replica `i ∉ F` achieves `CommittedLocal st i v s val`, then no valid `PreparedCert` for slot `s`
  in any view `v' ≥ v` carries a different value.
* `Cslib.Distributed.ByzantineQuorum.pbft_commit_agreement_idealAuth`: multi-slot SMR commit safety
  step—all honest replicas `i₁, i₂ ∉ F` commit identical values at every sequence slot `s`, even
  across distinct views `v₁` and `v₂`.
* `Cslib.Distributed.ByzantineQuorum.pbft_smr_state_agreement_idealAuth`: deterministic
  state-machine replicas executing committed slots `0, ..., k - 1` reach identical service states.
* `Cslib.Distributed.ByzantineQuorum.pbft_honest_primary_three_phase_liveness_idealAuth`:
  synchronized honest-primary 3-phase liveness step (after [CastroLiskov1999], §§4.2, 4.5.2)—when
  `primary v ∉ F` and all honest replicas are active in view `v` at a fresh slot `s`, synchronous
  delivery of `PrePrepare → Prepare → Commit` among `univ \ F` commits `(v, s, val)` at every honest
  replica.
* `Cslib.Distributed.ByzantineQuorum.exists_pbft_splitBrain_fin3`: `|P| ≤ 3 * f` split-brain
  view-change counterexample on `Fin 3` (`f = 1`, `F = {2}`), exhibiting a primary schedule and a
  reachable state in which honest replica `0` commits `some false` at slot `0` in view `0` while
  honest replica `1` commits `some true` at slot `0` in view `1`.

## References

* [M. Castro, B. Liskov, *Practical Byzantine Fault Tolerance*][CastroLiskov1999]
* [M. Castro, B. Liskov, *Practical Byzantine Fault Tolerance and Proactive
  Recovery*][CastroLiskov2002]
-/

public section

namespace Cslib.Distributed.ByzantineQuorum

open Finset

/-! ### Quorum size, certificates, and authenticated PBFT messages -/

/-- Byzantine quorum certificate size `|P| - f` (which equals `2 * f + 1` when `|P| = 3 * f + 1`
and satisfies dissemination intersection for every `3 * f < |P|`). -/
@[expose] def pbftQuorumSize (P : Type*) [Fintype P] (f : ℕ) : ℕ :=
  Fintype.card P - f

/-- A `(view, slot, val)` protocol entry stored in a replica's accepted or committed log, where
`val : Option V` represents either a client request `some r` or PBFT's `null` no-op `none`. -/
@[ext]
structure SlotEntry (V : Type*) where
  /-- View number in which `val` was proposed or committed. -/
  view : ℕ
  /-- Sequence number (slot) in the replicated log. -/
  slot : ℕ
  /-- Client request (`some r`) or `null` no-op (`none`). -/
  val : Option V
  deriving @[expose] DecidableEq

/-- A PBFT prepared certificate (`P_m` in [CastroLiskov1999], §§4.2, 4.4, pp. 4, 6) witnessing that
`primary view` pre-prepared `(view, slot, val)` and the backup replicas in `prepares` sent matching
`Prepare` messages. -/
@[ext]
structure PreparedCert (P V : Type*) where
  /-- View in which `(slot, val)` prepared. -/
  view : ℕ
  /-- Sequence slot prepared in `view`. -/
  slot : ℕ
  /-- Prepared slot value (`some r` or `none` for `null`). -/
  val : Option V
  /-- Backup replicas (`≠ primary view`) contributing matching `Prepare` messages. -/
  prepares : Finset P
  deriving @[expose] DecidableEq

/-- Full replica quorum `{primary c.view} ∪ c.prepares` vouching for prepared certificate `c`. -/
@[expose] def PreparedCert.voters {P V : Type*} [DecidableEq P]
    (primary : ℕ → P) (c : PreparedCert P V) : Finset P :=
  insert (primary c.view) c.prepares

/-- A `VIEW-CHANGE` payload sent by `sender` for target `view` carrying prepared certificates `pset`
from views `< view` ([CastroLiskov1999], §4.4, p. 6). -/
@[ext]
structure ViewChangeMsg (P V : Type*) where
  /-- New view number `v' > 0` requested by `sender`. -/
  view : ℕ
  /-- Replica signing the `VIEW-CHANGE` message. -/
  sender : P
  /-- Set of prepared certificates from earlier views reported by `sender`. -/
  pset : Finset (PreparedCert P V)
  deriving @[expose] DecidableEq

/-- A slot assignment `(slot, val)` computed in the `O` component of a `NEW-VIEW` message
([CastroLiskov1999], §4.4, p. 6). -/
@[ext]
structure SlotProposal (V : Type*) where
  /-- Sequence slot re-proposed upon entering the new view. -/
  slot : ℕ
  /-- Value from the highest prepared view in `Vset`, or `none` (`null` no-op) if unprepared. -/
  val : Option V
  deriving @[expose] DecidableEq

/-- Authenticated wire messages of normal-case and view-change PBFT ([CastroLiskov1999], §§4.2,
4.4, pp. 4–6). -/
inductive PBFTMsg (P V : Type*) where
  /-- `PRE-PREPARE(view, slot, val)` signed by `primary view`. -/
  | prePrepare (view slot : ℕ) (val : Option V)
  /-- `PREPARE(view, slot, val, sender)` signed by backup `sender`. -/
  | prepare (view slot : ℕ) (val : Option V) (sender : P)
  /-- `COMMIT(view, slot, val, sender)` signed by replica `sender`. -/
  | commit (view slot : ℕ) (val : Option V) (sender : P)
  /-- `VIEW-CHANGE` message signed by `vc.sender`. -/
  | viewChange (vc : ViewChangeMsg P V)
  /-- `NEW-VIEW(view, vset, oset)` signed by `primary view`. -/
  | newView (view : ℕ) (vset : Finset (ViewChangeMsg P V)) (oset : Finset (SlotProposal V))
  deriving @[expose] DecidableEq

/-- Authenticated signer required for a `PBFTMsg` under primary schedule `primary`. -/
@[expose] def PBFTMsg.signer {P V : Type*} (primary : ℕ → P) : PBFTMsg P V → P
  | .prePrepare v _ _ => primary v
  | .prepare _ _ _ i => i
  | .commit _ _ _ i => i
  | .viewChange vc => vc.sender
  | .newView v _ _ => primary v

/-! ### Certificate validation and deterministic `NEW-VIEW` `Oset` computation -/

/-- `c` is a valid prepared certificate over network log `net` when `primary c.view` sent the
matching `prePrepare`, `primary c.view ∉ c.prepares`, every `q ∈ c.prepares` sent a matching
`prepare`, and `{primary c.view} ∪ c.prepares` has size at least `pbftQuorumSize P f`. -/
@[expose] def PreparedCert.ValidIn {P V : Type*} [Fintype P] [DecidableEq P]
    (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V)) (c : PreparedCert P V) : Prop :=
  PBFTMsg.prePrepare c.view c.slot c.val ∈ net ∧
    primary c.view ∉ c.prepares ∧
    (∀ q ∈ c.prepares, PBFTMsg.prepare c.view c.slot c.val q ∈ net) ∧
    pbftQuorumSize P f ≤ (c.voters primary).card

instance instDecidablePreparedCertValidIn {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V))
    (c : PreparedCert P V) : Decidable (c.ValidIn primary f net) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `vc` is a valid `VIEW-CHANGE` message on `net` when `0 < vc.view`,
`PBFTMsg.viewChange vc ∈ net`, and every certificate in `vc.pset` is valid on `net` with view `<
vc.view`. -/
@[expose] def ViewChangeMsg.ValidIn {P V : Type*} [Fintype P] [DecidableEq P]
    (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V)) (vc : ViewChangeMsg P V) : Prop :=
  0 < vc.view ∧
    PBFTMsg.viewChange vc ∈ net ∧
    ∀ c ∈ vc.pset, c.view < vc.view ∧ c.ValidIn primary f net

instance instDecidableViewChangeValidIn {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V))
    (vc : ViewChangeMsg P V) : Decidable (vc.ValidIn primary f net) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Select the re-proposed slot value for slot `s` from the union `certs` of prepared certificates
in `Vset` ([CastroLiskov1999], §4.4, p. 6): returns `some none` (`null` no-op) if `certs` contains
no certificate for slot `s`, `some o` if all maximum-view certificates for slot `s` agree on `o`,
and `none` only if `certs` contains conflicting certificates at the same maximum view. -/
@[expose] def computeSlotVal {P V : Type*} [DecidableEq P] [DecidableEq V]
    (certs : Finset (PreparedCert P V)) (s : ℕ) : Option (Option V) :=
  let sc := certs.filter fun c => c.slot = s
  if sc = ∅ then
    some none
  else
    let topCerts := sc.filter fun c => ∀ c' ∈ sc, c'.view ≤ c.view
    let topVals := topCerts.image PreparedCert.val
    if h : topVals.card = 1 then
      some (topVals.choose (fun _ => True) (by
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
        exact ⟨x, ⟨by rw [hx]; exact Finset.mem_singleton_self x, trivial⟩,
          fun y hy => by rw [hx, Finset.mem_singleton] at hy; exact hy.1⟩))
    else
      none

/-- Compute the `O` set of `SlotProposal`s for `NEW-VIEW` from `vset` ([CastroLiskov1999], §4.4,
p. 6, with `min-s = 0`): empty if `vset` reports no prepared certificates, and otherwise covering
every slot `0 ≤ s ≤ max-s` via `computeSlotVal`. -/
@[expose] def computeOset {P V : Type*} [DecidableEq P] [DecidableEq V]
    (vset : Finset (ViewChangeMsg P V)) : Option (Finset (SlotProposal V)) :=
  let certs := vset.biUnion ViewChangeMsg.pset
  if hne : certs.Nonempty then
    let maxS := (certs.image PreparedCert.slot).max' (hne.image PreparedCert.slot)
    let slots := Finset.range (maxS + 1)
    if ∀ s ∈ slots, (computeSlotVal certs s).isSome then
      some (slots.biUnion fun s =>
        match computeSlotVal certs s with
        | some o => {⟨s, o⟩}
        | none => ∅)
    else
      none
  else
    some ∅

/-- Validity of `NEW-VIEW(v', vset, oset)` over `net` ([CastroLiskov1999], §4.4, p. 6): `0 < v'`,
`newView` and all corresponding `prePrepare` messages in `oset` are on `net`, every `vc ∈ vset` is a
valid `VIEW-CHANGE` for `v'`, at least `pbftQuorumSize P f` distinct replicas contributed to `vset`,
and `computeOset vset = some oset`. -/
@[expose] def NewViewValidIn {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V)) (v' : ℕ)
    (vset : Finset (ViewChangeMsg P V)) (oset : Finset (SlotProposal V)) : Prop :=
  0 < v' ∧
    PBFTMsg.newView v' vset oset ∈ net ∧
    (∀ prop ∈ oset, PBFTMsg.prePrepare v' prop.slot prop.val ∈ net) ∧
    (∀ vc ∈ vset, vc.view = v' ∧ vc.ValidIn primary f net) ∧
    pbftQuorumSize P f ≤ (vset.image ViewChangeMsg.sender).card ∧
    computeOset vset = some oset

instance instDecidableNewViewValidIn {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (primary : ℕ → P) (f : ℕ) (net : Finset (PBFTMsg P V)) (v' : ℕ)
    (vset : Finset (ViewChangeMsg P V)) (oset : Finset (SlotProposal V)) :
    Decidable (NewViewValidIn primary f net v' vset oset) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ### Ghost-free replica state and asynchronous PBFT transitions -/

/-- Local operational state of a PBFT replica ([CastroLiskov1999], §§4.2, 4.4). -/
@[ext]
structure ReplicaState (P V : Type*) where
  /-- Current active view (`0` initially). -/
  view : ℕ
  /-- `true` while the replica has halted normal-case processing awaiting `NEW-VIEW`. -/
  inViewChange : Bool
  /-- Highest view for which this replica has initiated `VIEW-CHANGE` or entered `NEW-VIEW`. -/
  targetView : ℕ
  /-- Accepted `(view, slot, val)` pre-prepares. -/
  accepted : Finset (SlotEntry V)
  /-- Valid `PreparedCert`s assembled by this replica across views. -/
  preparedCerts : Finset (PreparedCert P V)
  /-- Locally committed `(view, slot, val)` entries (`committed-local` in §4.2, p. 5). -/
  committed : Finset (SlotEntry V)
  deriving @[expose] DecidableEq

/-- Effective view watermark `targetView` (during a view change) or `view` (during normal case). -/
@[expose] def ReplicaState.effectiveView {P V : Type*} (r : ReplicaState P V) : ℕ :=
  if r.inViewChange then r.targetView else r.view

/-- Global asynchronous PBFT configuration: transmitted signed network messages and per-replica
states. -/
@[ext]
structure PBFTState (P V : Type*) where
  /-- Set of signed messages transmitted on the network (modeling arbitrary delay, reordering,
  replay, and selective link omission). -/
  network : Finset (PBFTMsg P V)
  /-- Local state of each replica; only entries for `i ∉ F` represent honest replicas. -/
  replicas : P → ReplicaState P V

/-- Initial PBFT global configuration in view `0` with empty logs and network. -/
@[expose] def initPBFTState (P V : Type*) : PBFTState P V where
  network := ∅
  replicas _ :=
    { view := 0
      inViewChange := false
      targetView := 0
      accepted := ∅
      preparedCerts := ∅
      committed := ∅ }

/-- Honest replica `i` has locally committed `(v, s, val)` in state `st`. -/
@[expose] def CommittedLocal {P V : Type*}
    (st : PBFTState P V) (i : P) (v s : ℕ) (val : Option V) : Prop :=
  ⟨v, s, val⟩ ∈ (st.replicas i).committed

instance instDecidableCommittedLocal {P V : Type*} [DecidableEq V]
    (st : PBFTState P V) (i : P) (v s : ℕ) (val : Option V) :
    Decidable (CommittedLocal st i v s val) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Atomic asynchronous step labels of the PBFT protocol. -/
inductive PBFTAction (P V : Type*) where
  /-- Primary `primary v` proposes `val` at fresh slot `s` in active view `v`. -/
  | propose (v s : ℕ) (val : Option V)
  /-- Backup `i ≠ primary v` accepts `prePrepare(v, s, val)` and emits `prepare(v, s, val, i)`. -/
  | acceptPrePrepare (i : P) (v s : ℕ) (val : Option V)
  /-- Replica `i` logs valid `PreparedCert` `c` in view `c.view` and emits `commit`. -/
  | completePrepare (i : P) (c : PreparedCert P V)
  /-- Replica `i` observes `pbftQuorumSize P f` matching `commit`s for prepared `c` and commits. -/
  | completeCommit (i : P) (c : PreparedCert P V) (committers : Finset P)
  /-- Replica `i` times out and initiates `VIEW-CHANGE` for `v' > effectiveView`. -/
  | startViewChange (i : P) (v' : ℕ)
  /-- Primary `primary v'` forms and broadcasts `NEW-VIEW(v', vset, oset)` and its `prePrepare`s. -/
  | formNewView (v' : ℕ) (vset : Finset (ViewChangeMsg P V))
  /-- Backup `i ≠ primary v'` validates `NEW-VIEW(v', vset, oset)`, enters `v'`, and emits
  `prepare`s for `oset`. -/
  | enterNewView (i : P) (v' : ℕ) (vset : Finset (ViewChangeMsg P V))
      (oset : Finset (SlotProposal V))
  /-- Faulty replica `m.signer primary ∈ F` injects signed message `m` onto the network. -/
  | byzSend (m : PBFTMsg P V)
  deriving @[expose] DecidableEq

/-- Computable single-step transition function of asynchronous PBFT under primary schedule
`primary`, fault parameter `f`, and static Byzantine set `F` (invalid actions stutter). -/
@[expose] def pbftStep {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (primary : ℕ → P) (f : ℕ) (F : Finset P) (st : PBFTState P V)
    (act : PBFTAction P V) : PBFTState P V :=
  match act with
  | .propose v s val =>
    let p := primary v
    let r := st.replicas p
    if p ∉ F ∧ r.view = v ∧ r.inViewChange = false ∧
        (r.accepted.filter fun e => e.view = v ∧ e.slot = s) = ∅ then
      { network := insert (PBFTMsg.prePrepare v s val) st.network
        replicas := Function.update st.replicas p
          { r with accepted := insert ⟨v, s, val⟩ r.accepted } }
    else st
  | .acceptPrePrepare i v s val =>
    let r := st.replicas i
    if i ∉ F ∧ i ≠ primary v ∧ r.view = v ∧ r.inViewChange = false ∧
        PBFTMsg.prePrepare v s val ∈ st.network ∧
        (r.accepted.filter fun e => e.view = v ∧ e.slot = s) = ∅ then
      { network := insert (PBFTMsg.prepare v s val i) st.network
        replicas := Function.update st.replicas i
          { r with accepted := insert ⟨v, s, val⟩ r.accepted } }
    else st
  | .completePrepare i c =>
    let r := st.replicas i
    if i ∉ F ∧ r.view = c.view ∧ r.inViewChange = false ∧
        ⟨c.view, c.slot, c.val⟩ ∈ r.accepted ∧ c.ValidIn primary f st.network then
      { network := insert (PBFTMsg.commit c.view c.slot c.val i) st.network
        replicas := Function.update st.replicas i
          { r with preparedCerts := insert c r.preparedCerts } }
    else st
  | .completeCommit i c committers =>
    let r := st.replicas i
    if i ∉ F ∧ r.view = c.view ∧ r.inViewChange = false ∧
        c ∈ r.preparedCerts ∧ pbftQuorumSize P f ≤ committers.card ∧
        (∀ q ∈ committers, PBFTMsg.commit c.view c.slot c.val q ∈ st.network) then
      { st with
        replicas := Function.update st.replicas i
          { r with committed := insert ⟨c.view, c.slot, c.val⟩ r.committed } }
    else st
  | .startViewChange i v' =>
    let r := st.replicas i
    if i ∉ F ∧ r.effectiveView < v' then
      let vc : ViewChangeMsg P V := ⟨v', i, r.preparedCerts⟩
      { network := insert (PBFTMsg.viewChange vc) st.network
        replicas := Function.update st.replicas i
          { r with inViewChange := true, targetView := v' } }
    else st
  | .formNewView v' vset =>
    let p := primary v'
    let r := st.replicas p
    match computeOset vset with
    | some oset =>
      if p ∉ F ∧ 0 < v' ∧ r.view < v' ∧ r.effectiveView ≤ v' ∧
          (∀ vc ∈ vset, vc.view = v' ∧ vc.ValidIn primary f st.network) ∧
          pbftQuorumSize P f ≤ (vset.image ViewChangeMsg.sender).card then
        let preMsgs := oset.image fun prop => PBFTMsg.prePrepare v' prop.slot prop.val
        let newEntries := oset.image fun prop => (⟨v', prop.slot, prop.val⟩ : SlotEntry V)
        { network := insert (PBFTMsg.newView v' vset oset) (st.network ∪ preMsgs)
          replicas := Function.update st.replicas p
            { r with
              view := v'
              inViewChange := false
              targetView := v'
              accepted := r.accepted ∪ newEntries } }
      else st
    | none => st
  | .enterNewView i v' vset oset =>
    let r := st.replicas i
    if i ∉ F ∧ i ≠ primary v' ∧ r.view < v' ∧ r.effectiveView ≤ v' ∧
        NewViewValidIn primary f st.network v' vset oset then
      let prepMsgs := oset.image fun prop => PBFTMsg.prepare v' prop.slot prop.val i
      let newEntries := oset.image fun prop => (⟨v', prop.slot, prop.val⟩ : SlotEntry V)
      { network := st.network ∪ prepMsgs
        replicas := Function.update st.replicas i
          { r with
            view := v'
            inViewChange := false
            targetView := v'
            accepted := r.accepted ∪ newEntries } }
    else st
  | .byzSend m =>
    if m.signer primary ∈ F then
      { st with network := insert m st.network }
    else st

/-- Inductive reachability of global PBFT states from `initPBFTState P V`. -/
inductive PBFTReachable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (primary : ℕ → P) (f : ℕ) (F : Finset P) : PBFTState P V → Prop where
  /-- The initial empty-network configuration in view `0` is reachable. -/
  | init : PBFTReachable primary f F (initPBFTState P V)
  /-- Stepping a reachable configuration along any `PBFTAction` yields a reachable configuration. -/
  | step {st : PBFTState P V} (act : PBFTAction P V) :
      PBFTReachable primary f F st →
      PBFTReachable primary f F (pbftStep primary f F st act)

/-- Fold a finite list of `PBFTAction`s from `st` preserves `PBFTReachable`. -/
theorem PBFTReachable.foldl_steps {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} {st : PBFTState P V}
    (hst : PBFTReachable primary f F st) (acts : List (PBFTAction P V)) :
    PBFTReachable primary f F (acts.foldl (pbftStep primary f F) st) := by
  induction acts generalizing st with
  | nil => exact hst
  | cons a as ih => exact ih (PBFTReachable.step a hst)

/-! ### Monotonicity helpers and inductive protocol invariants -/

section Invariants

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
  {primary : ℕ → P} {f : ℕ} {F : Finset P}

omit [DecidableEq V] in
private lemma PreparedCert.ValidIn.mono {net₁ net₂ : Finset (PBFTMsg P V)}
    (hsub : net₁ ⊆ net₂) {c : PreparedCert P V} (hc : c.ValidIn primary f net₁) :
    c.ValidIn primary f net₂ :=
  ⟨hsub hc.1, hc.2.1, fun q hq => hsub (hc.2.2.1 q hq), hc.2.2.2⟩

omit [DecidableEq V] in
private lemma ViewChangeMsg.ValidIn.mono {net₁ net₂ : Finset (PBFTMsg P V)}
    (hsub : net₁ ⊆ net₂) {vc : ViewChangeMsg P V} (hvc : vc.ValidIn primary f net₁) :
    vc.ValidIn primary f net₂ :=
  ⟨hvc.1, hsub hvc.2.1, fun c hc => ⟨(hvc.2.2 c hc).1, (hvc.2.2 c hc).2.mono hsub⟩⟩

private lemma NewViewValidIn.mono {net₁ net₂ : Finset (PBFTMsg P V)}
    (hsub : net₁ ⊆ net₂) {v' : ℕ} {vset : Finset (ViewChangeMsg P V)}
    {oset : Finset (SlotProposal V)}
    (hnv : NewViewValidIn primary f net₁ v' vset oset) :
    NewViewValidIn primary f net₂ v' vset oset :=
  ⟨hnv.1, hsub hnv.2.1, fun prop hp => hsub (hnv.2.2.1 prop hp),
    fun vc hvc => ⟨(hnv.2.2.2.1 vc hvc).1, (hnv.2.2.2.1 vc hvc).2.mono hsub⟩,
    hnv.2.2.2.2⟩

omit [Fintype P] in
private lemma computeOset_slot_unique {vset : Finset (ViewChangeMsg P V)}
    {oset : Finset (SlotProposal V)} (ho : computeOset vset = some oset)
    {p₁ p₂ : SlotProposal V} (hp₁ : p₁ ∈ oset) (hp₂ : p₂ ∈ oset) (hs : p₁.slot = p₂.slot) :
    p₁.val = p₂.val := by
  unfold computeOset at ho
  dsimp only at ho
  split_ifs at ho with hne hall
  · injection ho with ho'
    subst ho'
    rw [Finset.mem_biUnion] at hp₁ hp₂
    obtain ⟨s₁, _, hs₁⟩ := hp₁
    obtain ⟨s₂, _, hs₂⟩ := hp₂
    cases hcs₁ : computeSlotVal (vset.biUnion ViewChangeMsg.pset) s₁ <;>
      rw [hcs₁] at hs₁
    · exact absurd hs₁ (Finset.notMem_empty _)
    · rw [Finset.mem_singleton] at hs₁
      cases hcs₂ : computeSlotVal (vset.biUnion ViewChangeMsg.pset) s₂ <;>
        rw [hcs₂] at hs₂
      · exact absurd hs₂ (Finset.notMem_empty _)
      · rw [Finset.mem_singleton] at hs₂
        subst hs₁ hs₂
        dsimp only at hs
        subst hs
        rw [hcs₁] at hcs₂
        exact Option.some.inj hcs₂
  · injection ho with ho'
    subst ho'
    exact absurd hp₁ (Finset.notMem_empty _)

/-- Predicate recording that replica `i` sent a normal-case vote (`prePrepare` if primary, `prepare`
if backup) for `(v, s, val)` on `st.network`. -/
private def HonestVoted (primary : ℕ → P) (st : PBFTState P V) (i : P) (v s : ℕ)
    (val : Option V) : Prop :=
  (i = primary v ∧ PBFTMsg.prePrepare v s val ∈ st.network) ∨
    (i ≠ primary v ∧ PBFTMsg.prepare v s val i ∈ st.network)

/-- Bundled safety invariant maintained across all `PBFTReachable` configurations. -/
private structure PBFTInvariant (primary : ℕ → P) (f : ℕ) (F : Finset P)
    (st : PBFTState P V) : Prop where
  view_le_effective : ∀ i, i ∉ F → (st.replicas i).view ≤ (st.replicas i).effectiveView
  accepted_view_le : ∀ i, i ∉ F → ∀ e ∈ (st.replicas i).accepted, e.view ≤ (st.replicas i).view
  accepted_unique : ∀ i, i ∉ F → ∀ e₁ ∈ (st.replicas i).accepted,
    ∀ e₂ ∈ (st.replicas i).accepted, e₁.view = e₂.view → e₁.slot = e₂.slot → e₁.val = e₂.val
  voted_imp_accepted : ∀ i, i ∉ F → ∀ v s val,
    HonestVoted primary st i v s val → ⟨v, s, val⟩ ∈ (st.replicas i).accepted
  active_pos_newView : ∀ i, i ∉ F → 0 < (st.replicas i).view →
    ∃ vset oset, NewViewValidIn primary f st.network (st.replicas i).view vset oset ∧
      ∀ prop ∈ oset, ⟨(st.replicas i).view, prop.slot, prop.val⟩ ∈ (st.replicas i).accepted
  accepted_pos_newView : ∀ i, i ∉ F → ∀ e ∈ (st.replicas i).accepted, 0 < e.view →
    ∃ vset oset, NewViewValidIn primary f st.network e.view vset oset ∧
      ∀ prop ∈ oset, prop.slot = e.slot → e.val = prop.val
  prepared_valid : ∀ i, i ∉ F → ∀ c ∈ (st.replicas i).preparedCerts,
    c.ValidIn primary f st.network ∧ c.view ≤ (st.replicas i).effectiveView
  commit_has_cert : ∀ k, k ∉ F → ∀ v s val, PBFTMsg.commit v s val k ∈ st.network →
    v ≤ (st.replicas k).effectiveView ∧
      ∃ c ∈ (st.replicas k).preparedCerts, c.view = v ∧ c.slot = s ∧ c.val = val
  viewChange_le_effective : ∀ vc, vc.sender ∉ F → PBFTMsg.viewChange vc ∈ st.network →
    vc.view ≤ (st.replicas vc.sender).effectiveView
  viewChange_contains_commit : ∀ vc, vc.sender ∉ F → PBFTMsg.viewChange vc ∈ st.network →
    ∀ v s val, PBFTMsg.commit v s val vc.sender ∈ st.network → v < vc.view →
      ∃ c ∈ vc.pset, c.view = v ∧ c.slot = s ∧ c.val = val
  committed_witness : ∀ i, i ∉ F → ∀ e ∈ (st.replicas i).committed,
    ∃ (c : PreparedCert P V) (committers : Finset P),
      c.view = e.view ∧ c.slot = e.slot ∧ c.val = e.val ∧
      c.ValidIn primary f st.network ∧ pbftQuorumSize P f ≤ committers.card ∧
      ∀ q ∈ committers, PBFTMsg.commit e.view e.slot e.val q ∈ st.network

omit [DecidableEq V] in
private lemma filter_accepted_eq_empty_iff {acc : Finset (SlotEntry V)} {v s : ℕ} :
    (acc.filter fun e => e.view = v ∧ e.slot = s) = ∅ ↔
      ∀ e ∈ acc, e.view = v → e.slot = s → False := by
  rw [Finset.filter_eq_empty_iff]
  exact ⟨fun h e he hv hs => h he ⟨hv, hs⟩, fun h _ he ⟨hv, hs⟩ => h _ he hv hs⟩

private lemma PBFTInvariant.committed_witness_of_unchanged {st : PBFTState P V}
    (inv : PBFTInvariant primary f F st) {net' : Finset (PBFTMsg P V)}
    (hnet : st.network ⊆ net') {reps' : P → ReplicaState P V}
    (hcom : ∀ i, (reps' i).committed = (st.replicas i).committed) :
    ∀ i, i ∉ F → ∀ e ∈ (reps' i).committed,
      ∃ (c : PreparedCert P V) (committers : Finset P),
        c.view = e.view ∧ c.slot = e.slot ∧ c.val = e.val ∧
        c.ValidIn primary f net' ∧ pbftQuorumSize P f ≤ committers.card ∧
        ∀ q ∈ committers, PBFTMsg.commit e.view e.slot e.val q ∈ net' := by
  intro i hiF e he
  rw [hcom i] at he
  obtain ⟨c, comms, hv₀, hs₀, hval₀, hcval, hcard, hcm⟩ := inv.committed_witness i hiF e he
  exact ⟨c, comms, hv₀, hs₀, hval₀, hcval.mono hnet, hcard, fun q hq => hnet (hcm q hq)⟩

private lemma pbftInvariant_init : PBFTInvariant primary f F (initPBFTState P V) where
  view_le_effective _ _ := le_rfl
  accepted_view_le _ _ _ he := absurd he (Finset.notMem_empty _)
  accepted_unique _ _ _ he := absurd he (Finset.notMem_empty _)
  voted_imp_accepted _ _ _ _ _ hv := by
    rcases hv with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact absurd hm (Finset.notMem_empty _)
  active_pos_newView _ _ hpos := absurd hpos (lt_irrefl 0)
  accepted_pos_newView _ _ _ he := absurd he (Finset.notMem_empty _)
  prepared_valid _ _ _ hc := absurd hc (Finset.notMem_empty _)
  commit_has_cert _ _ _ _ _ hm := absurd hm (Finset.notMem_empty _)
  viewChange_le_effective _ _ hm := absurd hm (Finset.notMem_empty _)
  viewChange_contains_commit _ _ hm := absurd hm (Finset.notMem_empty _)
  committed_witness _ _ _ he := absurd he (Finset.notMem_empty _)

private lemma pbftInvariant_step {st : PBFTState P V}
    (inv : PBFTInvariant primary f F st) (act : PBFTAction P V) :
    PBFTInvariant primary f F (pbftStep primary f F st act) := by
  cases act with
  | propose v s val =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hpF, hpv, hpin, hfresh⟩ := hg
      rw [filter_accepted_eq_empty_iff] at hfresh
      have hnet_sub : st.network ⊆ insert (PBFTMsg.prePrepare v s val) st.network :=
        Finset.subset_insert _ _
      refine
        { view_le_effective := fun i hiF => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self]; exact inv.view_le_effective _ hpF
            · simp only [Function.update_of_ne hip]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self, Finset.mem_insert] at he ⊢
              rcases he with rfl | he'
              · exact le_of_eq hpv.symm
              · exact inv.accepted_view_le _ hpF e he'
            · simp only [Function.update_of_ne hip] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self, Finset.mem_insert] at he₁ he₂
              rcases he₁ with rfl | he₁' <;> rcases he₂ with rfl | he₂'
              · rfl
              · exact False.elim (hfresh e₂ he₂' hv.symm hs.symm)
              · exact False.elim (hfresh e₁ he₁' hv hs)
              · exact inv.accepted_unique _ hpF e₁ he₁' e₂ he₂' hv hs
            · simp only [Function.update_of_ne hip] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
            · rw [Finset.mem_insert] at hm
              rcases hm with hm_eq | hm_old
              · injection hm_eq with hv_eq hs_eq hval_eq
                subst hv_eq hs_eq hval_eq hi_eq
                simp only [Function.update_self, Finset.mem_insert, true_or]
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inl ⟨hi_eq, hm_old⟩)
                by_cases hip : i = primary v
                · subst hip; simp only [Function.update_self, Finset.mem_insert]; exact Or.inr hacc
                · simp only [Function.update_of_ne hip]; exact hacc
            · rw [Finset.mem_insert] at hm
              rcases hm with hm_eq | hm_old
              · exact nomatch hm_eq
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inr ⟨hi_ne, hm_old⟩)
                by_cases hip : i = primary v
                · subst hip; simp only [Function.update_self, Finset.mem_insert]; exact Or.inr hacc
                · simp only [Function.update_of_ne hip]; exact hacc
          active_pos_newView := fun i hiF hpos => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hpF hpos
              exact ⟨vset, oset, hnv.mono hnet_sub,
                fun prop hp => Finset.mem_insert_of_mem (hacc prop hp)⟩
            · simp only [Function.update_of_ne hip] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self, Finset.mem_insert] at he
              rcases he with rfl | he_old
              · dsimp only at hpos ⊢
                rw [← hpv] at hpos
                obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hpF hpos
                rw [hpv] at hnv hacc
                refine ⟨vset, oset, hnv.mono hnet_sub, fun prop hp hs => ?_⟩
                exact False.elim (hfresh _ (hacc prop hp) rfl hs)
              · obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView _ hpF e he_old hpos
                exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
            · simp only [Function.update_of_ne hip] at he
              obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid _ hpF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
            · simp only [Function.update_of_ne hip] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hkp : k = primary v
              · subst hkp; simp only [Function.update_self]
                exact inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
              · simp only [Function.update_of_ne hkp]
                exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
          viewChange_le_effective := fun vc hvcF hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hvp : vc.sender = primary v
              · rw [hvp]; simp only [Function.update_self]
                exact hvp ▸ inv.viewChange_le_effective vc hvcF hm_old
              · simp only [Function.update_of_ne hvp]
                exact inv.viewChange_le_effective vc hvcF hm_old
          viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
            rw [Finset.mem_insert] at hm hcm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · rcases hcm with hcm_eq | hcm_old
              · exact nomatch hcm_eq
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
            by_cases hip : i = primary v
            · subst hip; simp only [Function.update_self]
            · simp only [Function.update_of_ne hip] }
    · exact inv
  | acceptPrePrepare i₀ v s val =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, hi₀ne, hi₀v, hi₀in, _, hfresh⟩ := hg
      rw [filter_accepted_eq_empty_iff] at hfresh
      have hnet_sub : st.network ⊆ insert (PBFTMsg.prepare v s val i₀) st.network :=
        Finset.subset_insert _ _
      refine
        { view_le_effective := fun i hiF => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]; exact inv.view_le_effective _ hi₀F
            · simp only [Function.update_of_ne hii]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_insert] at he ⊢
              rcases he with rfl | he'
              · exact le_of_eq hi₀v.symm
              · exact inv.accepted_view_le _ hi₀F e he'
            · simp only [Function.update_of_ne hii] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_insert] at he₁ he₂
              rcases he₁ with rfl | he₁' <;> rcases he₂ with rfl | he₂'
              · rfl
              · exact False.elim (hfresh e₂ he₂' hv.symm hs.symm)
              · exact False.elim (hfresh e₁ he₁' hv hs)
              · exact inv.accepted_unique _ hi₀F e₁ he₁' e₂ he₂' hv hs
            · simp only [Function.update_of_ne hii] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
            · rw [Finset.mem_insert] at hm
              rcases hm with hm_eq | hm_old
              · exact nomatch hm_eq
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inl ⟨hi_eq, hm_old⟩)
                by_cases hii : i = i₀
                · subst hii; simp only [Function.update_self, Finset.mem_insert]; exact Or.inr hacc
                · simp only [Function.update_of_ne hii]; exact hacc
            · rw [Finset.mem_insert] at hm
              rcases hm with hm_eq | hm_old
              · injection hm_eq with hv_eq hs_eq hval_eq hi_eq
                subst hv_eq hs_eq hval_eq hi_eq
                simp only [Function.update_self, Finset.mem_insert, true_or]
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inr ⟨hi_ne, hm_old⟩)
                by_cases hii : i = i₀
                · subst hii; simp only [Function.update_self, Finset.mem_insert]; exact Or.inr hacc
                · simp only [Function.update_of_ne hii]; exact hacc
          active_pos_newView := fun i hiF hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hi₀F hpos
              exact ⟨vset, oset, hnv.mono hnet_sub,
                fun prop hp => Finset.mem_insert_of_mem (hacc prop hp)⟩
            · simp only [Function.update_of_ne hii] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_insert] at he
              rcases he with rfl | he_old
              · dsimp only at hpos ⊢
                rw [← hi₀v] at hpos
                obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hi₀F hpos
                rw [hi₀v] at hnv hacc
                refine ⟨vset, oset, hnv.mono hnet_sub, fun prop hp hs => ?_⟩
                exact False.elim (hfresh _ (hacc prop hp) rfl hs)
              · obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView _ hi₀F e he_old hpos
                exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
            · simp only [Function.update_of_ne hii] at he
              obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid _ hi₀F c hc
              exact ⟨hval.mono hnet_sub, hle⟩
            · simp only [Function.update_of_ne hii] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hki : k = i₀
              · subst hki; simp only [Function.update_self]
                exact inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
              · simp only [Function.update_of_ne hki]
                exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
          viewChange_le_effective := fun vc hvcF hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hvi : vc.sender = i₀
              · rw [hvi]; simp only [Function.update_self]
                exact hvi ▸ inv.viewChange_le_effective vc hvcF hm_old
              · simp only [Function.update_of_ne hvi]
                exact inv.viewChange_le_effective vc hvcF hm_old
          viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
            rw [Finset.mem_insert] at hm hcm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · rcases hcm with hcm_eq | hcm_old
              · exact nomatch hcm_eq
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
            · simp only [Function.update_of_ne hii] }
    · exact inv
  | completePrepare i₀ c₀ =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, hi₀v, hi₀in, _, hc₀val⟩ := hg
      have hnet_sub : st.network ⊆ insert (PBFTMsg.commit c₀.view c₀.slot c₀.val i₀) st.network :=
        Finset.subset_insert _ _
      have heff_eq : (st.replicas i₀).effectiveView = c₀.view := by
        simp only [ReplicaState.effectiveView, hi₀in, Bool.false_eq_true, ↓reduceIte, hi₀v]
      refine
        { view_le_effective := fun i hiF => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]; exact inv.view_le_effective _ hi₀F
            · simp only [Function.update_of_ne hii]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he ⊢
              exact inv.accepted_view_le _ hi₀F e he
            · simp only [Function.update_of_ne hii] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he₁ he₂
              exact inv.accepted_unique _ hi₀F e₁ he₁ e₂ he₂ hv hs
            · simp only [Function.update_of_ne hii] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            have hv_old : HonestVoted primary st i v₀ s₀ val₀ := by
              rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
              · rw [Finset.mem_insert] at hm
                rcases hm with hm_eq | hm_old
                · exact nomatch hm_eq
                · exact Or.inl ⟨hi_eq, hm_old⟩
              · rw [Finset.mem_insert] at hm
                rcases hm with hm_eq | hm_old
                · exact nomatch hm_eq
                · exact Or.inr ⟨hi_ne, hm_old⟩
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
              exact inv.voted_imp_accepted _ hi₀F v₀ s₀ val₀ hv_old
            · simp only [Function.update_of_ne hii]
              exact inv.voted_imp_accepted i hiF v₀ s₀ val₀ hv_old
          active_pos_newView := fun i hiF hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hi₀F hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
            · simp only [Function.update_of_ne hii] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            have he' : e ∈ (st.replicas i).accepted := by
              by_cases hii : i = i₀
              · subst hii; simpa only [Function.update_self] using he
              · simpa only [Function.update_of_ne hii] using he
            obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he' hpos
            exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_insert] at hc ⊢
              rcases hc with rfl | hc_old
              · exact ⟨hc₀val.mono hnet_sub, le_of_eq heff_eq.symm⟩
              · obtain ⟨hval, hle⟩ := inv.prepared_valid _ hi₀F c hc_old
                exact ⟨hval.mono hnet_sub, hle⟩
            · simp only [Function.update_of_ne hii] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · injection hm_eq with hv_eq hs_eq hval_eq hk_eq
              subst hv_eq hs_eq hval_eq hk_eq
              simp only [Function.update_self, Finset.mem_insert]
              exact ⟨le_of_eq heff_eq.symm, c₀, Or.inl rfl, rfl, rfl, rfl⟩
            · by_cases hki : k = i₀
              · subst hki; simp only [Function.update_self, Finset.mem_insert]
                obtain ⟨hle, c, hc, hv₀, hs₀, hval₀⟩ := inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
                exact ⟨hle, c, Or.inr hc, hv₀, hs₀, hval₀⟩
              · simp only [Function.update_of_ne hki]
                exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
          viewChange_le_effective := fun vc hvcF hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hvi : vc.sender = i₀
              · rw [hvi]; simp only [Function.update_self]
                exact hvi ▸ inv.viewChange_le_effective vc hvcF hm_old
              · simp only [Function.update_of_ne hvi]
                exact inv.viewChange_le_effective vc hvcF hm_old
          viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
            rw [Finset.mem_insert] at hm hcm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · rcases hcm with hcm_eq | hcm_old
              · injection hcm_eq with hv_eq hs_eq hval_eq hk_eq
                subst hv_eq hs_eq hval_eq
                have hle := inv.viewChange_le_effective vc hvcF hm_old
                rw [hk_eq, heff_eq] at hle
                omega
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
            · simp only [Function.update_of_ne hii] }
    · exact inv
  | completeCommit i₀ c₀ committers =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, _, _, hc₀mem, hcard, hcm_all⟩ := hg
      have hc₀val := (inv.prepared_valid i₀ hi₀F c₀ hc₀mem).1
      refine
        { view_le_effective := fun i hiF => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]; exact inv.view_le_effective _ hi₀F
            · simp only [Function.update_of_ne hii]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he ⊢
              exact inv.accepted_view_le _ hi₀F e he
            · simp only [Function.update_of_ne hii] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he₁ he₂
              exact inv.accepted_unique _ hi₀F e₁ he₁ e₂ he₂ hv hs
            · simp only [Function.update_of_ne hii] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
              exact inv.voted_imp_accepted _ hi₀F v₀ s₀ val₀ hv
            · simp only [Function.update_of_ne hii]
              exact inv.voted_imp_accepted i hiF v₀ s₀ val₀ hv
          active_pos_newView := fun i hiF hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hpos ⊢
              exact inv.active_pos_newView _ hi₀F hpos
            · simp only [Function.update_of_ne hii] at hpos ⊢
              exact inv.active_pos_newView i hiF hpos
          accepted_pos_newView := fun i hiF e he hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he
              exact inv.accepted_pos_newView _ hi₀F e he hpos
            · simp only [Function.update_of_ne hii] at he
              exact inv.accepted_pos_newView i hiF e he hpos
          prepared_valid := fun i hiF c hc => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hc ⊢
              exact inv.prepared_valid _ hi₀F c hc
            · simp only [Function.update_of_ne hii] at hc ⊢
              exact inv.prepared_valid i hiF c hc
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            by_cases hki : k = i₀
            · subst hki; simp only [Function.update_self]
              exact inv.commit_has_cert _ hkF v₀ s₀ val₀ hm
            · simp only [Function.update_of_ne hki]
              exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm
          viewChange_le_effective := fun vc hvcF hm => by
            by_cases hvi : vc.sender = i₀
            · rw [hvi]; simp only [Function.update_self]
              exact hvi ▸ inv.viewChange_le_effective vc hvcF hm
            · simp only [Function.update_of_ne hvi]
              exact inv.viewChange_le_effective vc hvcF hm
          viewChange_contains_commit := inv.viewChange_contains_commit
          committed_witness := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_insert] at he
              rcases he with rfl | he_old
              · exact ⟨c₀, committers, rfl, rfl, rfl, hc₀val, hcard, hcm_all⟩
              · exact inv.committed_witness _ hi₀F e he_old
            · simp only [Function.update_of_ne hii] at he
              exact inv.committed_witness i hiF e he }
    · exact inv
  | startViewChange i₀ v' =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, heff_lt⟩ := hg
      have hview_le_old := inv.view_le_effective i₀ hi₀F
      have hnet_sub :
          st.network ⊆ insert (PBFTMsg.viewChange ⟨v', i₀, (st.replicas i₀).preparedCerts⟩)
            st.network := Finset.subset_insert _ _
      refine
        { view_le_effective := fun i hiF => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, ReplicaState.effectiveView, ↓reduceIte]
              omega
            · simp only [Function.update_of_ne hii]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he ⊢
              exact inv.accepted_view_le _ hi₀F e he
            · simp only [Function.update_of_ne hii] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at he₁ he₂
              exact inv.accepted_unique _ hi₀F e₁ he₁ e₂ he₂ hv hs
            · simp only [Function.update_of_ne hii] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            have hv_old : HonestVoted primary st i v₀ s₀ val₀ := by
              rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
              · rw [Finset.mem_insert] at hm
                rcases hm with hm_eq | hm_old
                · exact nomatch hm_eq
                · exact Or.inl ⟨hi_eq, hm_old⟩
              · rw [Finset.mem_insert] at hm
                rcases hm with hm_eq | hm_old
                · exact nomatch hm_eq
                · exact Or.inr ⟨hi_ne, hm_old⟩
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
              exact inv.voted_imp_accepted _ hi₀F v₀ s₀ val₀ hv_old
            · simp only [Function.update_of_ne hii]
              exact inv.voted_imp_accepted i hiF v₀ s₀ val₀ hv_old
          active_pos_newView := fun i hiF hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hi₀F hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
            · simp only [Function.update_of_ne hii] at hpos ⊢
              obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
              exact ⟨vset, oset, hnv.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            have he' : e ∈ (st.replicas i).accepted := by
              by_cases hii : i = i₀
              · subst hii; simpa only [Function.update_self] using he
              · simpa only [Function.update_of_ne hii] using he
            obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he' hpos
            exact ⟨vset, oset, hnv.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            by_cases hii : i = i₀
            · subst hii
              simp only [Function.update_self, ReplicaState.effectiveView, ↓reduceIte] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid _ hi₀F c hc
              exact ⟨hval.mono hnet_sub, le_of_lt (lt_of_le_of_lt hle heff_lt)⟩
            · simp only [Function.update_of_ne hii] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · exact nomatch hm_eq
            · by_cases hki : k = i₀
              · subst hki; simp only [Function.update_self, ReplicaState.effectiveView, ↓reduceIte]
                obtain ⟨hle, c, hc⟩ := inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
                exact ⟨le_of_lt (lt_of_le_of_lt hle heff_lt), c, hc⟩
              · simp only [Function.update_of_ne hki]
                exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
          viewChange_le_effective := fun vc hvcF hm => by
            rw [Finset.mem_insert] at hm
            rcases hm with hm_eq | hm_old
            · injection hm_eq with hvc_eq
              subst hvc_eq
              simp only [Function.update_self, ReplicaState.effectiveView, ↓reduceIte, le_rfl]
            · by_cases hvi : vc.sender = i₀
              · rw [hvi]; simp only [Function.update_self, ReplicaState.effectiveView, ↓reduceIte]
                have hle := inv.viewChange_le_effective vc hvcF hm_old
                rw [hvi] at hle
                omega
              · simp only [Function.update_of_ne hvi]
                exact inv.viewChange_le_effective vc hvcF hm_old
          viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
            rw [Finset.mem_insert] at hm hcm
            rcases hcm with hcm_eq | hcm_old
            · exact nomatch hcm_eq
            · rcases hm with hm_eq | hm_old
              · injection hm_eq with hvc_eq
                subst hvc_eq
                obtain ⟨_, c, hc, hv₀, hs₀, hval₀⟩ :=
                  inv.commit_has_cert i₀ hi₀F v₀ s₀ val₀ hcm_old
                exact ⟨c, hc, hv₀, hs₀, hval₀⟩
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
            · simp only [Function.update_of_ne hii] }
    · exact inv
  | formNewView v' vset =>
    unfold pbftStep; dsimp only
    cases hoset : computeOset vset with
    | none => exact inv
    | some oset =>
      dsimp only
      split_ifs with hg
      · obtain ⟨hpF, hv'pos, hview_lt, heff_le, hvc_all, hvc_card⟩ := hg
        let preMsgs : Finset (PBFTMsg P V) :=
          oset.image fun prop => PBFTMsg.prePrepare v' prop.slot prop.val
        let net' := insert (PBFTMsg.newView v' vset oset) (st.network ∪ preMsgs)
        let newEntries := oset.image fun prop => (⟨v', prop.slot, prop.val⟩ : SlotEntry V)
        have hnet_sub : st.network ⊆ net' :=
          Finset.subset_union_left.trans (Finset.subset_insert _ _)
        have hnv_new : NewViewValidIn primary f net' v' vset oset := by
          refine ⟨hv'pos, Finset.mem_insert_self _ _, fun prop hp => ?_,
            fun vc hvc => ⟨(hvc_all vc hvc).1, (hvc_all vc hvc).2.mono hnet_sub⟩,
            hvc_card, hoset⟩
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨prop, hp, rfl⟩))
        refine
          { view_le_effective := fun i hiF => by
              by_cases hip : i = primary v'
              · subst hip
                simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                  ↓reduceIte, le_rfl]
              · simp only [Function.update_of_ne hip]; exact inv.view_le_effective i hiF
            accepted_view_le := fun i hiF e he => by
              by_cases hip : i = primary v'
              · subst hip; simp only [Function.update_self, Finset.mem_union] at he ⊢
                rcases he with he_old | he_new
                · exact le_trans (inv.accepted_view_le _ hpF e he_old) (le_of_lt hview_lt)
                · rw [Finset.mem_image] at he_new
                  obtain ⟨prop, _, rfl⟩ := he_new
                  exact le_rfl
              · simp only [Function.update_of_ne hip] at he ⊢
                exact inv.accepted_view_le i hiF e he
            accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
              by_cases hip : i = primary v'
              · subst hip; simp only [Function.update_self, Finset.mem_union] at he₁ he₂
                rcases he₁ with he₁_old | he₁_new <;> rcases he₂ with he₂_old | he₂_new
                · exact inv.accepted_unique _ hpF e₁ he₁_old e₂ he₂_old hv hs
                · rw [Finset.mem_image] at he₂_new
                  obtain ⟨p₂, _, rfl⟩ := he₂_new
                  have hle := inv.accepted_view_le _ hpF e₁ he₁_old
                  dsimp only at hv
                  omega
                · rw [Finset.mem_image] at he₁_new
                  obtain ⟨p₁, _, rfl⟩ := he₁_new
                  have hle := inv.accepted_view_le _ hpF e₂ he₂_old
                  dsimp only at hv
                  omega
                · rw [Finset.mem_image] at he₁_new he₂_new
                  obtain ⟨p₁, hp₁, rfl⟩ := he₁_new
                  obtain ⟨p₂, hp₂, rfl⟩ := he₂_new
                  exact computeOset_slot_unique hoset hp₁ hp₂ hs
              · simp only [Function.update_of_ne hip] at he₁ he₂
                exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
            voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
              rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
              · rw [Finset.mem_insert, Finset.mem_union] at hm
                rcases hm with hm_eq | hm_old | hm_pre
                · exact nomatch hm_eq
                · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inl ⟨hi_eq, hm_old⟩)
                  by_cases hip : i = primary v'
                  · subst hip; simp only [Function.update_self, Finset.mem_union]; exact Or.inl hacc
                  · simp only [Function.update_of_ne hip]; exact hacc
                · rw [Finset.mem_image] at hm_pre
                  obtain ⟨prop, hp, hpeq⟩ := hm_pre
                  injection hpeq with hv_eq hs_eq hval_eq
                  subst hv_eq hs_eq hval_eq hi_eq
                  simp only [Function.update_self, Finset.mem_union]
                  exact Or.inr (Finset.mem_image.mpr ⟨prop, hp, rfl⟩)
              · rw [Finset.mem_insert, Finset.mem_union] at hm
                rcases hm with hm_eq | hm_old | hm_pre
                · exact nomatch hm_eq
                · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inr ⟨hi_ne, hm_old⟩)
                  by_cases hip : i = primary v'
                  · subst hip; simp only [Function.update_self, Finset.mem_union]; exact Or.inl hacc
                  · simp only [Function.update_of_ne hip]; exact hacc
                · rw [Finset.mem_image] at hm_pre
                  obtain ⟨prop, _, hpeq⟩ := hm_pre
                  exact nomatch hpeq
            active_pos_newView := fun i hiF hpos => by
              by_cases hip : i = primary v'
              · subst hip; simp only [Function.update_self]
                refine ⟨vset, oset, hnv_new, fun prop hp => ?_⟩
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨prop, hp, rfl⟩)
              · simp only [Function.update_of_ne hip] at hpos ⊢
                obtain ⟨vs, os, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
                exact ⟨vs, os, hnv.mono hnet_sub, hacc⟩
            accepted_pos_newView := fun i hiF e he hpos => by
              by_cases hip : i = primary v'
              · subst hip; simp only [Function.update_self, Finset.mem_union] at he
                rcases he with he_old | he_new
                · obtain ⟨vs, os, hnv, hprop⟩ := inv.accepted_pos_newView _ hpF e he_old hpos
                  exact ⟨vs, os, hnv.mono hnet_sub, hprop⟩
                · rw [Finset.mem_image] at he_new
                  obtain ⟨prop₀, hp₀, rfl⟩ := he_new
                  refine ⟨vset, oset, hnv_new, fun prop hp hs => ?_⟩
                  exact computeOset_slot_unique hoset hp₀ hp hs.symm
              · simp only [Function.update_of_ne hip] at he
                obtain ⟨vs, os, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
                exact ⟨vs, os, hnv.mono hnet_sub, hprop⟩
            prepared_valid := fun i hiF c hc => by
              by_cases hip : i = primary v'
              · subst hip
                simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                  ↓reduceIte] at hc ⊢
                obtain ⟨hval, hle⟩ := inv.prepared_valid _ hpF c hc
                exact ⟨hval.mono hnet_sub, le_trans hle heff_le⟩
              · simp only [Function.update_of_ne hip] at hc ⊢
                obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
                exact ⟨hval.mono hnet_sub, hle⟩
            commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
              rw [Finset.mem_insert, Finset.mem_union] at hm
              rcases hm with hm_eq | hm_old | hm_pre
              · exact nomatch hm_eq
              · by_cases hkp : k = primary v'
                · subst hkp
                  simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                    ↓reduceIte]
                  obtain ⟨hle, c, hc⟩ := inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
                  exact ⟨le_trans hle heff_le, c, hc⟩
                · simp only [Function.update_of_ne hkp]
                  exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
              · rw [Finset.mem_image] at hm_pre
                obtain ⟨_, _, hpeq⟩ := hm_pre
                exact nomatch hpeq
            viewChange_le_effective := fun vc hvcF hm => by
              rw [Finset.mem_insert, Finset.mem_union] at hm
              rcases hm with hm_eq | hm_old | hm_pre
              · exact nomatch hm_eq
              · by_cases hvp : vc.sender = primary v'
                · rw [hvp]
                  simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                    ↓reduceIte]
                  have hle := inv.viewChange_le_effective vc hvcF hm_old
                  rw [hvp] at hle
                  exact le_trans hle heff_le
                · simp only [Function.update_of_ne hvp]
                  exact inv.viewChange_le_effective vc hvcF hm_old
              · rw [Finset.mem_image] at hm_pre
                obtain ⟨_, _, hpeq⟩ := hm_pre
                exact nomatch hpeq
            viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
              rw [Finset.mem_insert, Finset.mem_union] at hm hcm
              rcases hm with hm_eq | hm_old | hm_pre
              · exact nomatch hm_eq
              · rcases hcm with hcm_eq | hcm_old | hcm_pre
                · exact nomatch hcm_eq
                · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
                · rw [Finset.mem_image] at hcm_pre
                  obtain ⟨_, _, hpeq⟩ := hcm_pre
                  exact nomatch hpeq
              · rw [Finset.mem_image] at hm_pre
                obtain ⟨_, _, hpeq⟩ := hm_pre
                exact nomatch hpeq
            committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
              by_cases hip : i = primary v'
              · subst hip; simp only [Function.update_self]
              · simp only [Function.update_of_ne hip] }
      · exact inv
  | enterNewView i₀ v' vset oset =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, hi₀ne, hview_lt, heff_le, hnv⟩ := hg
      have hoset := hnv.2.2.2.2.2
      have hnet_sub :
          st.network ⊆
            st.network ∪ oset.image fun prop => PBFTMsg.prepare v' prop.slot prop.val i₀ :=
        Finset.subset_union_left
      refine
        { view_le_effective := fun i hiF => by
            by_cases hii : i = i₀
            · subst hii
              simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                ↓reduceIte, le_rfl]
            · simp only [Function.update_of_ne hii]; exact inv.view_le_effective i hiF
          accepted_view_le := fun i hiF e he => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_union] at he ⊢
              rcases he with he_old | he_new
              · exact le_trans (inv.accepted_view_le _ hi₀F e he_old) (le_of_lt hview_lt)
              · rw [Finset.mem_image] at he_new
                obtain ⟨prop, _, rfl⟩ := he_new
                exact le_rfl
            · simp only [Function.update_of_ne hii] at he ⊢
              exact inv.accepted_view_le i hiF e he
          accepted_unique := fun i hiF e₁ he₁ e₂ he₂ hv hs => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_union] at he₁ he₂
              rcases he₁ with he₁_old | he₁_new <;> rcases he₂ with he₂_old | he₂_new
              · exact inv.accepted_unique _ hi₀F e₁ he₁_old e₂ he₂_old hv hs
              · rw [Finset.mem_image] at he₂_new
                obtain ⟨p₂, _, rfl⟩ := he₂_new
                dsimp only at hv
                have hle := inv.accepted_view_le _ hi₀F e₁ he₁_old
                omega
              · rw [Finset.mem_image] at he₁_new
                obtain ⟨p₁, _, rfl⟩ := he₁_new
                dsimp only at hv
                have hle := inv.accepted_view_le _ hi₀F e₂ he₂_old
                omega
              · rw [Finset.mem_image] at he₁_new he₂_new
                obtain ⟨p₁, hp₁, rfl⟩ := he₁_new
                obtain ⟨p₂, hp₂, rfl⟩ := he₂_new
                exact computeOset_slot_unique hoset hp₁ hp₂ hs
            · simp only [Function.update_of_ne hii] at he₁ he₂
              exact inv.accepted_unique i hiF e₁ he₁ e₂ he₂ hv hs
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            rcases hv with ⟨hi_eq, hm⟩ | ⟨hi_ne, hm⟩
            · rw [Finset.mem_union] at hm
              rcases hm with hm_old | hm_prep
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inl ⟨hi_eq, hm_old⟩)
                by_cases hii : i = i₀
                · subst hii; simp only [Function.update_self, Finset.mem_union]; exact Or.inl hacc
                · simp only [Function.update_of_ne hii]; exact hacc
              · rw [Finset.mem_image] at hm_prep
                obtain ⟨_, _, hpeq⟩ := hm_prep
                exact nomatch hpeq
            · rw [Finset.mem_union] at hm
              rcases hm with hm_old | hm_prep
              · have hacc := inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inr ⟨hi_ne, hm_old⟩)
                by_cases hii : i = i₀
                · subst hii; simp only [Function.update_self, Finset.mem_union]; exact Or.inl hacc
                · simp only [Function.update_of_ne hii]; exact hacc
              · rw [Finset.mem_image] at hm_prep
                obtain ⟨prop, hp, hpeq⟩ := hm_prep
                injection hpeq with hv_eq hs_eq hval_eq hi_eq
                subst hv_eq hs_eq hval_eq hi_eq
                simp only [Function.update_self, Finset.mem_union]
                exact Or.inr (Finset.mem_image.mpr ⟨prop, hp, rfl⟩)
          active_pos_newView := fun i hiF hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
              refine ⟨vset, oset, hnv.mono hnet_sub, fun prop hp => ?_⟩
              exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨prop, hp, rfl⟩)
            · simp only [Function.update_of_ne hii] at hpos ⊢
              obtain ⟨vs, os, hnv₀, hacc⟩ := inv.active_pos_newView i hiF hpos
              exact ⟨vs, os, hnv₀.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self, Finset.mem_union] at he
              rcases he with he_old | he_new
              · obtain ⟨vs, os, hnv₀, hprop⟩ := inv.accepted_pos_newView _ hi₀F e he_old hpos
                exact ⟨vs, os, hnv₀.mono hnet_sub, hprop⟩
              · rw [Finset.mem_image] at he_new
                obtain ⟨prop₀, hp₀, rfl⟩ := he_new
                refine ⟨vset, oset, hnv.mono hnet_sub, fun prop hp hs => ?_⟩
                exact computeOset_slot_unique hoset hp₀ hp hs.symm
            · simp only [Function.update_of_ne hii] at he
              obtain ⟨vs, os, hnv₀, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
              exact ⟨vs, os, hnv₀.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            by_cases hii : i = i₀
            · subst hii
              simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                ↓reduceIte] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid _ hi₀F c hc
              exact ⟨hval.mono hnet_sub, le_trans hle heff_le⟩
            · simp only [Function.update_of_ne hii] at hc ⊢
              obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
              exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm => by
            rw [Finset.mem_union] at hm
            rcases hm with hm_old | hm_prep
            · by_cases hki : k = i₀
              · subst hki
                simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                  ↓reduceIte]
                obtain ⟨hle, c, hc⟩ := inv.commit_has_cert _ hkF v₀ s₀ val₀ hm_old
                exact ⟨le_trans hle heff_le, c, hc⟩
              · simp only [Function.update_of_ne hki]
                exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
            · rw [Finset.mem_image] at hm_prep
              obtain ⟨_, _, hpeq⟩ := hm_prep
              exact nomatch hpeq
          viewChange_le_effective := fun vc hvcF hm => by
            rw [Finset.mem_union] at hm
            rcases hm with hm_old | hm_prep
            · by_cases hvi : vc.sender = i₀
              · rw [hvi]
                simp only [Function.update_self, ReplicaState.effectiveView, Bool.false_eq_true,
                  ↓reduceIte]
                have hle := inv.viewChange_le_effective vc hvcF hm_old
                rw [hvi] at hle
                exact le_trans hle heff_le
              · simp only [Function.update_of_ne hvi]
                exact inv.viewChange_le_effective vc hvcF hm_old
            · rw [Finset.mem_image] at hm_prep
              obtain ⟨_, _, hpeq⟩ := hm_prep
              exact nomatch hpeq
          viewChange_contains_commit := fun vc hvcF hm v₀ s₀ val₀ hcm hlt => by
            rw [Finset.mem_union] at hm hcm
            rcases hm with hm_old | hm_prep
            · rcases hcm with hcm_old | hcm_prep
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
              · rw [Finset.mem_image] at hcm_prep
                obtain ⟨_, _, hpeq⟩ := hcm_prep
                exact nomatch hpeq
            · rw [Finset.mem_image] at hm_prep
              obtain ⟨_, _, hpeq⟩ := hm_prep
              exact nomatch hpeq
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun i => by
            by_cases hii : i = i₀
            · subst hii; simp only [Function.update_self]
            · simp only [Function.update_of_ne hii] }
    · exact inv
  | byzSend m =>
    unfold pbftStep; dsimp only
    split_ifs with hmF
    · have hnet_sub : st.network ⊆ insert m st.network := Finset.subset_insert _ _
      refine
        { view_le_effective := inv.view_le_effective
          accepted_view_le := inv.accepted_view_le
          accepted_unique := inv.accepted_unique
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv => by
            rcases hv with ⟨hi_eq, hm_mem⟩ | ⟨hi_ne, hm_mem⟩
            · rw [Finset.mem_insert] at hm_mem
              rcases hm_mem with rfl | hm_old
              · simp only [PBFTMsg.signer] at hmF
                exact absurd (hi_eq ▸ hmF) hiF
              · exact inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inl ⟨hi_eq, hm_old⟩)
            · rw [Finset.mem_insert] at hm_mem
              rcases hm_mem with rfl | hm_old
              · simp only [PBFTMsg.signer] at hmF
                exact absurd hmF hiF
              · exact inv.voted_imp_accepted i hiF v₀ s₀ val₀ (Or.inr ⟨hi_ne, hm_old⟩)
          active_pos_newView := fun i hiF hpos => by
            obtain ⟨vs, os, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
            exact ⟨vs, os, hnv.mono hnet_sub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos => by
            obtain ⟨vs, os, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
            exact ⟨vs, os, hnv.mono hnet_sub, hprop⟩
          prepared_valid := fun i hiF c hc => by
            obtain ⟨hval, hle⟩ := inv.prepared_valid i hiF c hc
            exact ⟨hval.mono hnet_sub, hle⟩
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm_mem => by
            rw [Finset.mem_insert] at hm_mem
            rcases hm_mem with rfl | hm_old
            · simp only [PBFTMsg.signer] at hmF
              exact absurd hmF hkF
            · exact inv.commit_has_cert k hkF v₀ s₀ val₀ hm_old
          viewChange_le_effective := fun vc hvcF hm_mem => by
            rw [Finset.mem_insert] at hm_mem
            rcases hm_mem with rfl | hm_old
            · simp only [PBFTMsg.signer] at hmF
              exact absurd hmF hvcF
            · exact inv.viewChange_le_effective vc hvcF hm_old
          viewChange_contains_commit := fun vc hvcF hm_mem v₀ s₀ val₀ hcm_mem hlt => by
            rw [Finset.mem_insert] at hm_mem hcm_mem
            rcases hm_mem with rfl | hm_old
            · simp only [PBFTMsg.signer] at hmF
              exact absurd hmF hvcF
            · rcases hcm_mem with rfl | hcm_old
              · simp only [PBFTMsg.signer] at hmF
                exact absurd hmF hvcF
              · exact inv.viewChange_contains_commit vc hvcF hm_old v₀ s₀ val₀ hcm_old hlt
          committed_witness := inv.committed_witness_of_unchanged hnet_sub fun _ => rfl }
    · exact inv

private lemma PBFTReachable.invariant {st : PBFTState P V}
    (hst : PBFTReachable primary f F st) : PBFTInvariant primary f F st := by
  induction hst with
  | init => exact pbftInvariant_init
  | step act _ ih => exact pbftInvariant_step ih act

omit [DecidableEq V] in
private lemma PreparedCert.ValidIn.voter_honestVoted {st : PBFTState P V} {c : PreparedCert P V}
    (hc : c.ValidIn primary f st.network) {q : P} (hq : q ∈ c.voters primary) :
    HonestVoted primary st q c.view c.slot c.val := by
  rw [PreparedCert.voters, Finset.mem_insert] at hq
  rcases hq with rfl | hq_prep
  · exact Or.inl ⟨rfl, hc.1⟩
  · have hne : q ≠ primary c.view := fun heq => hc.2.1 (heq ▸ hq_prep)
    exact Or.inr ⟨hne, hc.2.2.1 q hq_prep⟩

end Invariants

/-! ### Within-view non-equivocation, cross-view commit preservation, and SMR safety -/

/-- Within-view non-equivocation step toward `#7506` (after [Castro and Liskov, §4.2,
p. 4][CastroLiskov1999]; ideal-authentication checkpoint-free model): under `3 * f < Fintype.card P`
and `F.card ≤ f`, any two valid `PreparedCert`s in a reachable state `st` for the same `view` and
`slot` have equal `val`. -/
theorem preparedCert_unique_idealAuth {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {c₁ c₂ : PreparedCert P V}
    (hc₁ : c₁.ValidIn primary f st.network) (hc₂ : c₂.ValidIn primary f st.network)
    (hv : c₁.view = c₂.view) (hs : c₁.slot = c₂.slot) :
    c₁.val = c₂.val := by
  have hdissem := isThresholdDisseminationQuorumSystem_thresholdQuorums_sub (P := P) hn
  have hmem₁ : c₁.voters primary ∈ (thresholdQuorums P (pbftQuorumSize P f)).quorums :=
    mem_thresholdQuorums_iff.mpr hc₁.2.2.2
  have hmem₂ : c₂.voters primary ∈ (thresholdQuorums P (pbftQuorumSize P f)).quorums :=
    mem_thresholdQuorums_iff.mpr hc₂.2.2.2
  obtain ⟨i, hi⟩ := hdissem.2 _ hmem₁ _ hmem₂ F hF
  rw [Finset.mem_sdiff, Finset.mem_inter] at hi
  have inv := hst.invariant
  have hacc₁ := inv.voted_imp_accepted i hi.2 c₁.view c₁.slot c₁.val (hc₁.voter_honestVoted hi.1.1)
  have hacc₂ := inv.voted_imp_accepted i hi.2 c₂.view c₂.slot c₂.val (hc₂.voter_honestVoted hi.1.2)
  exact inv.accepted_unique i hi.2 _ hacc₁ _ hacc₂ hv hs

/-- Cross-view commit-preservation step toward `#7506` (after [Castro and Liskov, §4.5.1,
pp. 6–7][CastroLiskov1999]; ideal-authentication checkpoint-free model): if `3 * f < Fintype.card
P`, `F.card ≤ f`, and some honest replica `i₀ ∉ F` locally commits `(v, s, val)` in reachable state
`st`, then every valid `PreparedCert` `c'` on `st.network` at slot `s` in any view `v' ≥ v` carries
`c'.val = val`. -/
theorem committedLocal_preserves_higher_prepared_idealAuth {P V : Type*} [Fintype P]
    [DecidableEq P] [DecidableEq V] {primary : ℕ → P} {f : ℕ} {F : Finset P}
    (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {i₀ : P} (hi₀ : i₀ ∉ F) {v s : ℕ} {val : Option V}
    (hcom : CommittedLocal st i₀ v s val) :
    ∀ {v' : ℕ}, v ≤ v' → ∀ {c' : PreparedCert P V},
      c'.ValidIn primary f st.network → c'.view = v' → c'.slot = s → c'.val = val := by
  have inv := hst.invariant
  obtain ⟨c₀, committers, hc₀v, hc₀s, hc₀val, hc₀valid, hcomm_card, hcomm_msgs⟩ :=
    inv.committed_witness i₀ hi₀ ⟨v, s, val⟩ hcom
  dsimp only at hc₀v hc₀s hc₀val hcomm_msgs
  have hdissem := isThresholdDisseminationQuorumSystem_thresholdQuorums_sub (P := P) hn
  intro v'
  induction v' using Nat.strong_induction_on with
  | ind v' ih =>
    intro hvle c' hc'valid hc'v hc's
    rcases eq_or_lt_of_le hvle with rfl | hvlt
    · rw [← hc₀val]
      exact preparedCert_unique_idealAuth hn hF hst hc'valid hc₀valid
        (hc'v.trans hc₀v.symm) (hc's.trans hc₀s.symm)
    · have hv'pos : 0 < v' := lt_of_le_of_lt (Nat.zero_le v) hvlt
      -- Honest voter `m ∉ F` in `c'.voters` accepted `(v', s, c'.val)` via a valid `NewView`.
      have hmem_c' : c'.voters primary ∈ (thresholdQuorums P (pbftQuorumSize P f)).quorums :=
        mem_thresholdQuorums_iff.mpr hc'valid.2.2.2
      obtain ⟨m, hm⟩ := hdissem.2 _ hmem_c' _ hmem_c' F hF
      rw [Finset.mem_sdiff, Finset.mem_inter] at hm
      have hm_acc := inv.voted_imp_accepted m hm.2 c'.view c'.slot c'.val
        (hc'valid.voter_honestVoted hm.1.1)
      rw [hc'v, hc's] at hm_acc
      obtain ⟨vset, oset, hnv, hoset_match⟩ := inv.accepted_pos_newView m hm.2 _ hm_acc hv'pos
      dsimp only at hnv hoset_match
      -- Quorum intersection between `committers` and `vset` senders yields an honest `k ∉ F`.
      have hmem_comm : committers ∈ (thresholdQuorums P (pbftQuorumSize P f)).quorums :=
        mem_thresholdQuorums_iff.mpr hcomm_card
      have hmem_vc :
          vset.image ViewChangeMsg.sender ∈ (thresholdQuorums P (pbftQuorumSize P f)).quorums :=
        mem_thresholdQuorums_iff.mpr hnv.2.2.2.2.1
      obtain ⟨k, hk⟩ := hdissem.2 _ hmem_comm _ hmem_vc F hF
      rw [Finset.mem_sdiff, Finset.mem_inter] at hk
      obtain ⟨⟨hk_comm, hk_img⟩, hkF⟩ := hk
      rw [Finset.mem_image] at hk_img
      obtain ⟨vc_k, hvc_k_mem, hvc_k_sender⟩ := hk_img
      obtain ⟨hvc_k_view, hvc_k_val⟩ := hnv.2.2.2.1 vc_k hvc_k_mem
      have hcm_k : PBFTMsg.commit v s val vc_k.sender ∈ st.network := by
        rw [hvc_k_sender]; exact hcomm_msgs k hk_comm
      obtain ⟨c_k, hc_k_pset, hc_k_v, hc_k_s, hc_k_val⟩ :=
        inv.viewChange_contains_commit vc_k (hvc_k_sender ▸ hkF) hvc_k_val.2.1
          v s val hcm_k (hvc_k_view ▸ hvlt)
      -- Inspect `computeOset vset = some oset` at slot `s`: `c_k` witnesses `s ≤ maxS` and
      -- non-empty `sc`.
      let certs := vset.biUnion ViewChangeMsg.pset
      have hc_k_certs : c_k ∈ certs := Finset.mem_biUnion.mpr ⟨vc_k, hvc_k_mem, hc_k_pset⟩
      have hcerts_ne : certs.Nonempty := ⟨c_k, hc_k_certs⟩
      have hoset_eq := hnv.2.2.2.2.2
      unfold computeOset at hoset_eq
      dsimp only at hoset_eq
      split_ifs at hoset_eq with hne_certs hall
      · injection hoset_eq with hoset_def
        have hs_le_max : s ≤ (certs.image PreparedCert.slot).max' (hne_certs.image _) := by
          rw [← hc_k_s]
          exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ hc_k_certs)
        have hs_in_slots :
            s ∈ Finset.range ((certs.image PreparedCert.slot).max' (hne_certs.image _) + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le hs_le_max)
        obtain ⟨o_s, ho_s⟩ := Option.isSome_iff_exists.mp (hall s hs_in_slots)
        have hprop_mem : (⟨s, o_s⟩ : SlotProposal V) ∈ oset := by
          rw [← hoset_def, Finset.mem_biUnion]
          refine ⟨s, hs_in_slots, ?_⟩
          rw [ho_s]
          exact Finset.mem_singleton_self _
        have hc'val_eq : c'.val = o_s := hoset_match ⟨s, o_s⟩ hprop_mem rfl
        -- Unpack `computeSlotVal certs s = some o_s` to find a max-view certificate `c_max`.
        let sc := certs.filter fun c => c.slot = s
        have hc_k_sc : c_k ∈ sc := Finset.mem_filter.mpr ⟨hc_k_certs, hc_k_s⟩
        have hsc_ne_empty : sc ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨c_k, hc_k_sc⟩
        unfold computeSlotVal at ho_s
        dsimp only at ho_s
        split_ifs at ho_s with hsc_eq hcard1
        · exact absurd hsc_eq hsc_ne_empty
        · injection ho_s with ho_s_eq
          generalize_proofs hp at ho_s_eq
          have hspec := (Finset.choose_spec (fun _ => True) _ hp).1
          rw [ho_s_eq, Finset.mem_image] at hspec
          obtain ⟨c_max, hc_max_top, hc_max_val⟩ := hspec
          rw [Finset.mem_filter] at hc_max_top
          obtain ⟨hc_max_sc, hc_max_ge⟩ := hc_max_top
          rw [Finset.mem_filter] at hc_max_sc
          obtain ⟨hc_max_certs, hc_max_s⟩ := hc_max_sc
          have hv_le_cmax : v ≤ c_max.view := hc_k_v ▸ hc_max_ge c_k hc_k_sc
          rw [Finset.mem_biUnion] at hc_max_certs
          obtain ⟨vc_m, hvc_m_mem, hc_max_pset⟩ := hc_max_certs
          obtain ⟨hvc_m_view, hvc_m_val⟩ := hnv.2.2.2.1 vc_m hvc_m_mem
          obtain ⟨hc_max_lt, hc_max_valid⟩ := hvc_m_val.2.2 c_max hc_max_pset
          have hc_max_lt_v' : c_max.view < v' := hvc_m_view ▸ hc_max_lt
          have hc_max_eq_val : c_max.val = val :=
            ih c_max.view hc_max_lt_v' hv_le_cmax hc_max_valid rfl hc_max_s
          exact hc'val_eq.trans (hc_max_val.symm.trans hc_max_eq_val)
      · exact absurd hcerts_ne hne_certs

/-- Multi-slot total-order SMR commit safety step toward `#7506` (after [Castro and Liskov, §4.5.1,
pp. 6–7][CastroLiskov1999]; ideal-authentication checkpoint-free model): under `3 * f <
Fintype.card P` and `F.card ≤ f`, any two honest replicas `i₁, i₂ ∉ F` that locally commit `(v₁, s,
val₁)` and `(v₂, s, val₂)` at sequence slot `s` (even in distinct views) commit `val₁ = val₂`. -/
theorem pbft_commit_agreement_idealAuth {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {i₁ i₂ : P} (hi₁ : i₁ ∉ F) (hi₂ : i₂ ∉ F)
    {v₁ v₂ s : ℕ} {val₁ val₂ : Option V}
    (hcom₁ : CommittedLocal st i₁ v₁ s val₁) (hcom₂ : CommittedLocal st i₂ v₂ s val₂) :
    val₁ = val₂ := by
  have inv := hst.invariant
  rcases le_total v₁ v₂ with hle | hle
  · obtain ⟨c₂, _, hc₂v, hc₂s, hc₂val, hc₂valid, _, _⟩ :=
      inv.committed_witness i₂ hi₂ ⟨v₂, s, val₂⟩ hcom₂
    dsimp only at hc₂v hc₂s hc₂val
    rw [← hc₂val]
    exact (committedLocal_preserves_higher_prepared_idealAuth hn hF hst hi₁ hcom₁ hle hc₂valid
      hc₂v hc₂s).symm
  · obtain ⟨c₁, _, hc₁v, hc₁s, hc₁val, hc₁valid, _, _⟩ :=
      inv.committed_witness i₁ hi₁ ⟨v₁, s, val₁⟩ hcom₁
    dsimp only at hc₁v hc₁s hc₁val
    rw [← hc₁val]
    exact committedLocal_preserves_higher_prepared_idealAuth hn hF hst hi₂ hcom₂ hle hc₁valid
      hc₁v hc₁s

/-- Sequential execution of deterministic state-machine commands `smStep : S → V → S` across slots
`0, ..., k - 1` (`none` = PBFT `null` no-op leaving the service state unchanged). -/
@[expose] def executeSlotLog {S V : Type*} (smInit : S) (smStep : S → V → S)
    (slotCmd : ℕ → Option V) : ℕ → S
  | 0 => smInit
  | k + 1 =>
    let prev := executeSlotLog smInit smStep slotCmd k
    match slotCmd k with
    | some cmd => smStep prev cmd
    | none => prev

/-- Deterministic state-machine replication state-agreement step toward `#7506` (after
[Castro and Liskov, §§3, 4.5.1, pp. 2–3, 6–7][CastroLiskov1999]; ideal-authentication
checkpoint-free model): if two honest replicas `i₁, i₂ ∉ F` have committed views
`views₁, views₂ : ℕ → ℕ` and slot commands `cmds₁, cmds₂` across all slots `< k` in reachable state
`st` (`3 * f < Fintype.card P`, `F.card ≤ f`), then executing slots `0, ..., k - 1` from `smInit`
yields identical service states at `i₁` and `i₂`. -/
theorem pbft_smr_state_agreement_idealAuth {P S V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {primary : ℕ → P} {f : ℕ} {F : Finset P}
    (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
    {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {i₁ i₂ : P} (hi₁ : i₁ ∉ F) (hi₂ : i₂ ∉ F)
    (smInit : S) (smStep : S → V → S)
    {views₁ views₂ : ℕ → ℕ} {cmds₁ cmds₂ : ℕ → Option V} {k : ℕ}
    (h₁ : ∀ s < k, CommittedLocal st i₁ (views₁ s) s (cmds₁ s))
    (h₂ : ∀ s < k, CommittedLocal st i₂ (views₂ s) s (cmds₂ s)) :
    executeSlotLog smInit smStep cmds₁ k = executeSlotLog smInit smStep cmds₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [executeSlotLog]
    have hprev := ih (fun s hs => h₁ s (Nat.lt_succ_of_lt hs))
      (fun s hs => h₂ s (Nat.lt_succ_of_lt hs))
    have hcmd := pbft_commit_agreement_idealAuth hn hF hst hi₁ hi₂
      (h₁ k (Nat.lt_succ_self k)) (h₂ k (Nat.lt_succ_self k))
    rw [hprev, hcmd]

/-! ### Synchronized honest-primary 3-phase liveness -/

/-- Computable 3-phase normal-case action schedule for view `v` and slot `s` given a duplicate-free
replica enumeration `enumP`:
1. `primary v` proposes `(v, s, val)` (`PrePrepare`),
2. every honest backup `j ∈ (univ \ F).erase (primary v)` accepts and broadcasts `Prepare`,
3. every honest replica `i ∈ univ \ F` assembles `PreparedCert` and broadcasts `Commit`, and then
   locally commits `(v, s, val)`. -/
private def honestPrimaryThreePhaseActions {P V : Type*} [Fintype P] [DecidableEq P]
    (primary : ℕ → P) (F : Finset P) (enumP : List P) (v s : ℕ)
    (val : Option V) : List (PBFTAction P V) :=
  let honest := Finset.univ \ F
  let backups := honest.erase (primary v)
  let cert : PreparedCert P V := ⟨v, s, val, backups⟩
  let honestList := enumP.filter fun i => decide (i ∉ F)
  let backupList := enumP.filter fun j => decide (j ∉ F ∧ j ≠ primary v)
  [PBFTAction.propose v s val] ++
    backupList.map (fun j => PBFTAction.acceptPrePrepare j v s val) ++
    honestList.map (fun i => PBFTAction.completePrepare i cert) ++
    honestList.map (fun i => PBFTAction.completeCommit i cert honest)

private lemma foldl_acceptPrePrepare {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} {v s : ℕ} {val : Option V}
    (bs : List P) (hnodup : bs.Nodup)
    (hbs : ∀ j ∈ bs, j ∉ F ∧ j ≠ primary v)
    (st : PBFTState P V)
    (hpre : PBFTMsg.prePrepare v s val ∈ st.network)
    (hactive : ∀ j ∈ bs, (st.replicas j).view = v ∧ (st.replicas j).inViewChange = false ∧
      ∀ e ∈ (st.replicas j).accepted, e.view = v → e.slot = s → False) :
    let st' := (bs.map fun j => PBFTAction.acceptPrePrepare j v s val).foldl
      (pbftStep primary f F) st
    st.network ⊆ st'.network ∧
      (∀ j ∈ bs, PBFTMsg.prepare v s val j ∈ st'.network ∧
        ⟨v, s, val⟩ ∈ (st'.replicas j).accepted ∧
        (st'.replicas j).view = v ∧ (st'.replicas j).inViewChange = false) ∧
      (∀ k, k ∉ bs → st'.replicas k = st.replicas k) := by
  induction bs generalizing st with
  | nil =>
    exact ⟨Subset.rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [List.nodup_cons] at hnodup
    obtain ⟨hb_not_mem, hnodup_bs⟩ := hnodup
    obtain ⟨hbF, hb_ne⟩ := hbs b List.mem_cons_self
    obtain ⟨hb_v, hb_in, hb_fresh⟩ := hactive b List.mem_cons_self
    have hempty : ((st.replicas b).accepted.filter fun e => e.view = v ∧ e.slot = s) = ∅ :=
      filter_accepted_eq_empty_iff.mpr hb_fresh
    let st₁ := pbftStep primary f F st (PBFTAction.acceptPrePrepare b v s val)
    have hst₁_eq : st₁ =
        { network := insert (PBFTMsg.prepare v s val b) st.network
          replicas := Function.update st.replicas b
            { st.replicas b with accepted := insert ⟨v, s, val⟩ (st.replicas b).accepted } } := by
      unfold st₁ pbftStep; dsimp only
      split_ifs with hg
      · rfl
      · exact absurd ⟨hbF, hb_ne, hb_v, hb_in, hpre, hempty⟩ hg
    have hpre₁ : PBFTMsg.prePrepare v s val ∈ st₁.network := by
      rw [hst₁_eq]; exact Finset.mem_insert_of_mem hpre
    have hactive₁ : ∀ j ∈ bs, (st₁.replicas j).view = v ∧ (st₁.replicas j).inViewChange = false ∧
        ∀ e ∈ (st₁.replicas j).accepted, e.view = v → e.slot = s → False := by
      intro j hj
      have hjne : j ≠ b := fun heq => hb_not_mem (heq ▸ hj)
      rw [hst₁_eq]; simp only [Function.update_of_ne hjne]
      exact hactive j (List.mem_cons_of_mem b hj)
    have hsub₁ : st.network ⊆ st₁.network := by rw [hst₁_eq]; exact Finset.subset_insert _ _
    obtain ⟨hnet_sub, hbs_post, hother⟩ :=
      ih hnodup_bs (fun j hj => hbs j (List.mem_cons_of_mem b hj)) st₁ hpre₁ hactive₁
    refine ⟨hsub₁.trans hnet_sub, fun j hj => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj_bs
      · have hrep_eq : (List.foldl (pbftStep primary f F) st₁
            (List.map (fun j => PBFTAction.acceptPrePrepare j v s val) bs)).replicas j =
            st₁.replicas j := hother j hb_not_mem
        rw [hrep_eq, hst₁_eq]
        simp only [Function.update_self, Finset.mem_insert, true_or]
        exact ⟨hnet_sub (by rw [hst₁_eq]; exact Finset.mem_insert_self _ _), trivial, hb_v, hb_in⟩
      · exact hbs_post j hj_bs
    · have hkb : k ≠ b := fun heq => hk (heq ▸ List.mem_cons_self)
      have hkbs : k ∉ bs := fun hm => hk (List.mem_cons_of_mem b hm)
      have hrep_eq := hother k hkbs
      rw [hrep_eq, hst₁_eq]
      exact Function.update_of_ne hkb _ _

private lemma foldl_completePrepare {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} {c : PreparedCert P V}
    (hs : List P) (hnodup : hs.Nodup)
    (hhs : ∀ i ∈ hs, i ∉ F)
    (st : PBFTState P V)
    (hc_valid : c.ValidIn primary f st.network)
    (hready : ∀ i ∈ hs, (st.replicas i).view = c.view ∧ (st.replicas i).inViewChange = false ∧
      ⟨c.view, c.slot, c.val⟩ ∈ (st.replicas i).accepted) :
    let st' := (hs.map fun i => PBFTAction.completePrepare i c).foldl (pbftStep primary f F) st
    st.network ⊆ st'.network ∧
      (∀ i ∈ hs, PBFTMsg.commit c.view c.slot c.val i ∈ st'.network ∧
        c ∈ (st'.replicas i).preparedCerts ∧
        (st'.replicas i).view = c.view ∧ (st'.replicas i).inViewChange = false) ∧
      (∀ k, k ∉ hs → st'.replicas k = st.replicas k) := by
  induction hs generalizing st with
  | nil =>
    exact ⟨Subset.rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | cons i hs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [List.nodup_cons] at hnodup
    obtain ⟨hi_not_mem, hnodup_hs⟩ := hnodup
    have hiF := hhs i List.mem_cons_self
    obtain ⟨hi_v, hi_in, hi_acc⟩ := hready i List.mem_cons_self
    let st₁ := pbftStep primary f F st (PBFTAction.completePrepare i c)
    have hst₁_eq : st₁ =
        { network := insert (PBFTMsg.commit c.view c.slot c.val i) st.network
          replicas := Function.update st.replicas i
            { st.replicas i with preparedCerts := insert c (st.replicas i).preparedCerts } } := by
      unfold st₁ pbftStep; dsimp only
      simp only [hiF, not_false_eq_true, hi_v, hi_in, hi_acc, hc_valid, and_self, ↓reduceIte]
    have hsub₁ : st.network ⊆ st₁.network := by rw [hst₁_eq]; exact Finset.subset_insert _ _
    have hready₁ : ∀ j ∈ hs, (st₁.replicas j).view = c.view ∧
        (st₁.replicas j).inViewChange = false ∧
        ⟨c.view, c.slot, c.val⟩ ∈ (st₁.replicas j).accepted := by
      intro j hj
      have hjne : j ≠ i := fun heq => hi_not_mem (heq ▸ hj)
      rw [hst₁_eq]; simp only [Function.update_of_ne hjne]
      exact hready j (List.mem_cons_of_mem i hj)
    obtain ⟨hnet_sub, hhs_post, hother⟩ :=
      ih hnodup_hs (fun j hj => hhs j (List.mem_cons_of_mem i hj)) st₁ (hc_valid.mono hsub₁) hready₁
    refine ⟨hsub₁.trans hnet_sub, fun j hj => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj_hs
      · have hrep_eq := hother j hi_not_mem
        rw [hrep_eq, hst₁_eq]
        simp only [Function.update_self, Finset.mem_insert, true_or]
        exact ⟨hnet_sub (by rw [hst₁_eq]; exact Finset.mem_insert_self _ _), trivial, hi_v, hi_in⟩
      · exact hhs_post j hj_hs
    · have hki : k ≠ i := fun heq => hk (heq ▸ List.mem_cons_self)
      have hkhs : k ∉ hs := fun hm => hk (List.mem_cons_of_mem i hm)
      have hrep_eq := hother k hkhs
      rw [hrep_eq, hst₁_eq]
      exact Function.update_of_ne hki _ _

private lemma foldl_completeCommit {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} {c : PreparedCert P V} {committers : Finset P}
    (hs : List P) (hnodup : hs.Nodup)
    (hhs : ∀ i ∈ hs, i ∉ F)
    (st : PBFTState P V)
    (hcard : pbftQuorumSize P f ≤ committers.card)
    (hcm : ∀ q ∈ committers, PBFTMsg.commit c.view c.slot c.val q ∈ st.network)
    (hready : ∀ i ∈ hs, (st.replicas i).view = c.view ∧ (st.replicas i).inViewChange = false ∧
      c ∈ (st.replicas i).preparedCerts) :
    let st' := (hs.map fun i => PBFTAction.completeCommit i c committers).foldl
      (pbftStep primary f F) st
    (∀ i ∈ hs, CommittedLocal st' i c.view c.slot c.val) ∧
      (∀ k, k ∉ hs → st'.replicas k = st.replicas k) := by
  induction hs generalizing st with
  | nil =>
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | cons i hs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [List.nodup_cons] at hnodup
    obtain ⟨hi_not_mem, hnodup_hs⟩ := hnodup
    have hiF := hhs i List.mem_cons_self
    obtain ⟨hi_v, hi_in, hi_prep⟩ := hready i List.mem_cons_self
    let st₁ := pbftStep primary f F st (PBFTAction.completeCommit i c committers)
    have hst₁_eq : st₁ =
        { st with
          replicas := Function.update st.replicas i
            { st.replicas i with
              committed := insert ⟨c.view, c.slot, c.val⟩ (st.replicas i).committed } } := by
      unfold st₁ pbftStep; dsimp only
      have hall : ∀ q ∈ committers, PBFTMsg.commit c.view c.slot c.val q ∈ st.network := hcm
      split_ifs with hg
      · rfl
      · exact absurd ⟨hiF, hi_v, hi_in, hi_prep, hcard, hall⟩ hg
    have hcm₁ : ∀ q ∈ committers, PBFTMsg.commit c.view c.slot c.val q ∈ st₁.network := by
      rw [hst₁_eq]; exact hcm
    have hready₁ : ∀ j ∈ hs, (st₁.replicas j).view = c.view ∧
        (st₁.replicas j).inViewChange = false ∧ c ∈ (st₁.replicas j).preparedCerts := by
      intro j hj
      have hjne : j ≠ i := fun heq => hi_not_mem (heq ▸ hj)
      rw [hst₁_eq]; simp only [Function.update_of_ne hjne]
      exact hready j (List.mem_cons_of_mem i hj)
    obtain ⟨hhs_post, hother⟩ :=
      ih hnodup_hs (fun j hj => hhs j (List.mem_cons_of_mem i hj)) st₁ hcm₁ hready₁
    refine ⟨fun j hj => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj_hs
      · unfold CommittedLocal
        have hrep_eq := hother j hi_not_mem
        rw [hrep_eq, hst₁_eq]
        simp only [Function.update_self, Finset.mem_insert, true_or]
      · exact hhs_post j hj_hs
    · have hki : k ≠ i := fun heq => hk (heq ▸ List.mem_cons_self)
      have hkhs : k ∉ hs := fun hm => hk (List.mem_cons_of_mem i hm)
      have hrep_eq := hother k hkhs
      rw [hrep_eq, hst₁_eq]
      exact Function.update_of_ne hki _ _

/-- Computable 3-phase liveness along `honestPrimaryThreePhaseActions` for any duplicate-free full
enumeration `enumP` of `P`. -/
private lemma pbft_honestPrimaryThreePhaseActions_commits {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {primary : ℕ → P} {f : ℕ} {F : Finset P}
    (hF : F.card ≤ f) {enumP : List P} (hnodup : enumP.Nodup) (hfull : ∀ i : P, i ∈ enumP)
    {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {v s : ℕ} (val : Option V) (hp_honest : primary v ∉ F)
    (hactive : ∀ i, i ∉ F → (st.replicas i).view = v ∧ (st.replicas i).inViewChange = false)
    (hfresh : ∀ i, i ∉ F → ∀ e ∈ (st.replicas i).accepted, e.view = v → e.slot = s → False) :
    let st' := (honestPrimaryThreePhaseActions primary F enumP v s val).foldl
      (pbftStep primary f F) st
    PBFTReachable primary f F st' ∧ ∀ i, i ∉ F → CommittedLocal st' i v s val := by
  let honest := Finset.univ \ F
  let backups := honest.erase (primary v)
  let cert : PreparedCert P V := ⟨v, s, val, backups⟩
  let honestList := enumP.filter fun i => decide (i ∉ F)
  let backupList := enumP.filter fun j => decide (j ∉ F ∧ j ≠ primary v)
  let sched := honestPrimaryThreePhaseActions primary F enumP v s val
  refine ⟨hst.foldl_steps sched, ?_⟩
  change ∀ i, i ∉ F → CommittedLocal (sched.foldl (pbftStep primary f F) st) i v s val
  unfold sched honestPrimaryThreePhaseActions
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- Phase 1a: honest primary proposes `(v, s, val)`.
  let st₁ := pbftStep primary f F st (PBFTAction.propose v s val)
  obtain ⟨hp_v, hp_in⟩ := hactive (primary v) hp_honest
  have hp_empty : (((st.replicas (primary v)).accepted).filter fun e => e.view = v ∧ e.slot = s) =
      ∅ := filter_accepted_eq_empty_iff.mpr (hfresh (primary v) hp_honest)
  have hst₁_eq : st₁ =
      { network := insert (PBFTMsg.prePrepare v s val) st.network
        replicas := Function.update st.replicas (primary v)
          { st.replicas (primary v) with
            accepted := insert ⟨v, s, val⟩ (st.replicas (primary v)).accepted } } := by
    unfold st₁ pbftStep; dsimp only
    simp only [hp_honest, not_false_eq_true, hp_v, hp_in, hp_empty, and_self, ↓reduceIte]
  -- Phase 1b: all honest backups accept `PrePrepare` and emit `Prepare`.
  have hbs_mem : ∀ j ∈ backupList, j ∉ F ∧ j ≠ primary v := by
    intro j hj
    have hdec := (List.mem_filter.mp hj).2
    exact of_decide_eq_true hdec
  have hbs_active : ∀ j ∈ backupList, (st₁.replicas j).view = v ∧
      (st₁.replicas j).inViewChange = false ∧
      ∀ e ∈ (st₁.replicas j).accepted, e.view = v → e.slot = s → False := by
    intro j hj
    obtain ⟨hjF, hjne⟩ := hbs_mem j hj
    have hrep : st₁.replicas j = st.replicas j := by
      rw [hst₁_eq]; exact Function.update_of_ne hjne _ _
    rw [hrep]
    exact ⟨(hactive j hjF).1, (hactive j hjF).2, hfresh j hjF⟩
  obtain ⟨hnet₁₂, hbs_post, hp_unchanged⟩ :=
    foldl_acceptPrePrepare (primary := primary) (f := f) (F := F)
      (v := v) (s := s) (val := val) backupList (hnodup.filter _) hbs_mem st₁
      (by rw [hst₁_eq]; exact Finset.mem_insert_self _ _) hbs_active
  let st₂ := (backupList.map fun j => PBFTAction.acceptPrePrepare j v s val).foldl
    (pbftStep primary f F) st₁
  -- Phase 2: `cert` is valid on `st₂.network`; all honest replicas assemble `cert` and emit
  -- `Commit`.
  have hhonest_card : pbftQuorumSize P f ≤ honest.card := by
    rw [pbftQuorumSize, Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ]
    omega
  have hvoters_eq : cert.voters primary = honest := by
    simp only [PreparedCert.voters, cert, backups]
    exact Finset.insert_erase (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp_honest⟩)
  have hcert_valid : cert.ValidIn primary f st₂.network := by
    refine ⟨hnet₁₂ (by rw [hst₁_eq]; exact Finset.mem_insert_self _ _),
      Finset.notMem_erase _ _, fun q hq => ?_, by rw [hvoters_eq]; exact hhonest_card⟩
    rw [Finset.mem_erase, Finset.mem_sdiff] at hq
    have hq_bl : q ∈ backupList :=
      List.mem_filter.mpr ⟨hfull q, decide_eq_true ⟨hq.2.2, hq.1⟩⟩
    exact (hbs_post q hq_bl).1
  have hhonest_mem : ∀ i ∈ honestList, i ∉ F := by
    intro i hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hprep_ready : ∀ i ∈ honestList, (st₂.replicas i).view = cert.view ∧
      (st₂.replicas i).inViewChange = false ∧
      ⟨cert.view, cert.slot, cert.val⟩ ∈ (st₂.replicas i).accepted := by
    intro i hi
    have hiF := hhonest_mem i hi
    by_cases hip : i = primary v
    · subst hip
      have hnot_bs : primary v ∉ backupList := fun hm => (hbs_mem _ hm).2 rfl
      rw [hp_unchanged (primary v) hnot_bs, hst₁_eq]
      simp only [Function.update_self, Finset.mem_insert, true_or, cert]
      exact ⟨hp_v, hp_in, trivial⟩
    · have hib : i ∈ backupList :=
        List.mem_filter.mpr ⟨hfull i, decide_eq_true ⟨hiF, hip⟩⟩
      obtain ⟨_, hacc, hv_i, hin_i⟩ := hbs_post i hib
      exact ⟨hv_i, hin_i, hacc⟩
  obtain ⟨_, hprep_post, _⟩ :=
    foldl_completePrepare (primary := primary) (f := f) (F := F) (c := cert)
      honestList (hnodup.filter _) hhonest_mem st₂ hcert_valid hprep_ready
  let st₃ := (honestList.map fun i => PBFTAction.completePrepare i cert).foldl
    (pbftStep primary f F) st₂
  -- Phase 3: all honest replicas observe `honest` commits (`≥ pbftQuorumSize P f`) and commit
  -- locally.
  have hcm_all : ∀ q ∈ honest, PBFTMsg.commit cert.view cert.slot cert.val q ∈ st₃.network := by
    intro q hq
    have hqF := (Finset.mem_sdiff.mp hq).2
    exact (hprep_post q (List.mem_filter.mpr ⟨hfull q, decide_eq_true hqF⟩)).1
  have hcom_ready : ∀ i ∈ honestList, (st₃.replicas i).view = cert.view ∧
      (st₃.replicas i).inViewChange = false ∧ cert ∈ (st₃.replicas i).preparedCerts := by
    intro i hi
    obtain ⟨_, hc_in, hv_i, hin_i⟩ := hprep_post i hi
    exact ⟨hv_i, hin_i, hc_in⟩
  obtain ⟨hcom_post, _⟩ :=
    foldl_completeCommit (primary := primary) (f := f) (F := F) (c := cert) (committers := honest)
      honestList (hnodup.filter _) hhonest_mem st₃ hhonest_card hcm_all hcom_ready
  intro i hiF
  exact hcom_post i (List.mem_filter.mpr ⟨hfull i, decide_eq_true hiF⟩)

/-- Synchronized honest-primary 3-phase liveness step toward `#7506` (after [Castro and Liskov,
§§4.2, 4.5.2, pp. 4–5, 7][CastroLiskov1999]; ideal-authentication checkpoint-free model): from any
reachable configuration `st` (`F.card ≤ f`) in which `primary v ∉ F` and every honest replica `i ∉
F` is active in view `v` (`view = v`, `inViewChange = false`) with fresh slot `s`, there exists a
finite 3-phase normal-case schedule reaching a configuration `st'` in which **every** honest
replica `i ∉ F` has locally committed `(v, s, val)`. -/
theorem pbft_honest_primary_three_phase_liveness_idealAuth {P V : Type*} [Fintype P]
    [DecidableEq P] [DecidableEq V] {primary : ℕ → P} {f : ℕ} {F : Finset P}
    (hF : F.card ≤ f) {st : PBFTState P V} (hst : PBFTReachable primary f F st)
    {v s : ℕ} (val : Option V) (hp_honest : primary v ∉ F)
    (hactive : ∀ i, i ∉ F → (st.replicas i).view = v ∧ (st.replicas i).inViewChange = false)
    (hfresh : ∀ i, i ∉ F → ∀ e ∈ (st.replicas i).accepted, e.view = v → e.slot = s → False) :
    ∃ acts : List (PBFTAction P V),
      let st' := acts.foldl (pbftStep primary f F) st
      PBFTReachable primary f F st' ∧ ∀ i, i ∉ F → CommittedLocal st' i v s val := by
  let enumP := (Finset.univ : Finset P).toList
  exact ⟨honestPrimaryThreePhaseActions primary F enumP v s val,
    pbft_honestPrimaryThreePhaseActions_commits hF (Finset.nodup_toList _)
      (fun i => Finset.mem_toList.mpr (Finset.mem_univ i)) hst val hp_honest hactive hfresh⟩

/-! ### `|P| ≤ 3 * f` split-brain view-change counterexample (`Fin 3, f = 1`) -/

/-- Round-robin primary schedule `v mod 3` on `Fin 3`. -/
private def fin3Primary (v : ℕ) : Fin 3 :=
  ⟨v % 3, Nat.mod_lt v (by decide)⟩

/-- Concrete 13-step PBFT execution on `Fin 3` with `f = 1` and faulty replica `F = {2}`
(`|P| = 3 ≤ 3 * f`): honest replica `0` (`primary 0`) commits `some false` at slot `0` in view `0`
using `{0, 2}`, faulty `2` omits its prepared certificate in `VIEW-CHANGE` to view `1`, and honest
replica `1` (`primary 1`) commits `some true` at slot `0` in view `1` using `{1, 2}`. -/
private def splitBrainTraceFin3 : List (PBFTAction (Fin 3) Bool) :=
  let cert₀ : PreparedCert (Fin 3) Bool := ⟨0, 0, some false, {2}⟩
  let vset₁ : Finset (ViewChangeMsg (Fin 3) Bool) := {⟨1, 1, ∅⟩, ⟨1, 2, ∅⟩}
  let cert₁ : PreparedCert (Fin 3) Bool := ⟨1, 0, some true, {2}⟩
  [ PBFTAction.propose 0 0 (some false)
  , PBFTAction.byzSend (PBFTMsg.prepare 0 0 (some false) 2)
  , PBFTAction.completePrepare 0 cert₀
  , PBFTAction.byzSend (PBFTMsg.commit 0 0 (some false) 2)
  , PBFTAction.completeCommit 0 cert₀ {0, 2}
  , PBFTAction.startViewChange 1 1
  , PBFTAction.byzSend (PBFTMsg.viewChange ⟨1, 2, ∅⟩)
  , PBFTAction.formNewView 1 vset₁
  , PBFTAction.propose 1 0 (some true)
  , PBFTAction.byzSend (PBFTMsg.prepare 1 0 (some true) 2)
  , PBFTAction.completePrepare 1 cert₁
  , PBFTAction.byzSend (PBFTMsg.commit 1 0 (some true) 2)
  , PBFTAction.completeCommit 1 cert₁ {1, 2} ]

/-- Sharpness of `3 * f < Fintype.card P` for PBFT view-change safety (`#7506`): on `Fin 3` with
`f = 1` (`Fintype.card (Fin 3) = 3 * f`) and static Byzantine set `F = {2}` (`F.card = 1 ≤ f`),
there exist a primary schedule `primary` and a reachable PBFT state in which honest replicas `0 ∉ F`
and `1 ∉ F` locally commit conflicting client requests `some false ≠ some true` at sequence slot
`0`. -/
theorem exists_pbft_splitBrain_fin3 :
    let F : Finset (Fin 3) := {2}
    F.card ≤ 1 ∧ (0 : Fin 3) ∉ F ∧ (1 : Fin 3) ∉ F ∧
      ∃ (primary : ℕ → Fin 3) (st : PBFTState (Fin 3) Bool),
        PBFTReachable primary 1 F st ∧
        CommittedLocal st 0 0 0 (some false) ∧
        CommittedLocal st 1 1 0 (some true) := by
  refine ⟨by decide, by decide, by decide, fin3Primary,
    splitBrainTraceFin3.foldl (pbftStep fin3Primary 1 {2}) (initPBFTState (Fin 3) Bool),
    PBFTReachable.init.foldl_steps splitBrainTraceFin3, ?_, ?_⟩
  · decide
  · decide

end Cslib.Distributed.ByzantineQuorum
