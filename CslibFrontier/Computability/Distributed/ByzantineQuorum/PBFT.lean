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

omit [Fintype P] [DecidableEq V] in
/-- An entry of replica `j` after replica `i` moves to `r'` was there before, or `j = i` and the
entry is new in `r'`. -/
private lemma mem_update_replica {α : Type*} (sel : ReplicaState P V → Finset α)
    {reps : P → ReplicaState P V} {i j : P} {r' : ReplicaState P V} {x : α}
    (h : x ∈ sel (Function.update reps i r' j)) :
    x ∈ sel (reps j) ∨ j = i ∧ x ∈ sel r' ∧ x ∉ sel (reps i) := by
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self] at h
    by_cases hx : x ∈ sel (reps j)
    exacts [Or.inl hx, Or.inr ⟨rfl, h, hx⟩]
  · rw [Function.update_of_ne hj] at h
    exact Or.inl h

omit [Fintype P] [DecidableEq V] in
/-- A quantity of replica `j` that does not decrease when replica `i` moves to `r'`. -/
private lemma le_update_replica {β : Type*} [Preorder β] (sel : ReplicaState P V → β)
    {reps : P → ReplicaState P V} {i : P} {r' : ReplicaState P V} (h : sel (reps i) ≤ sel r')
    (j : P) : sel (reps j) ≤ sel (Function.update reps i r' j) := by
  rcases eq_or_ne j i with rfl | hj
  · rwa [Function.update_self]
  · rw [Function.update_of_ne hj]

omit [Fintype P] [DecidableEq P] [DecidableEq V] in
/-- What honest replica `i`, moving from local state `r` to `r'` in a step that leaves the network
`net'`, guarantees about a message it sends in that step. -/
private def FreshMsgOK (r r' : ReplicaState P V) (i : P) (net' : Finset (PBFTMsg P V)) :
    PBFTMsg P V → Prop
  | .prePrepare v s val | .prepare v s val _ => ⟨v, s, val⟩ ∈ r'.accepted
  | .commit v s val _ => r.effectiveView ≤ v ∧ v ≤ r'.effectiveView ∧
      ∃ c ∈ r'.preparedCerts, c.view = v ∧ c.slot = s ∧ c.val = val
  | .viewChange vc => vc.view ≤ r'.effectiveView ∧
      ∀ v s val, PBFTMsg.commit v s val i ∈ net' → v < vc.view →
        ∃ c ∈ vc.pset, c.view = v ∧ c.slot = s ∧ c.val = val
  | .newView _ _ _ => True

/-- The invariant survives a step in which honest replica `i` moves to the local state `r'`, the
other replicas stay put and the network grows to `net'`. The step may only raise the views of `i`
and add to what it has accepted, prepared and committed; the hypotheses `h_…` are the clauses of
the invariant about what is new: the entries and certificates of `r'` that `i` did not have, the
view it enters, and the messages it sends. -/
private lemma PBFTInvariant.of_replica_update {st : PBFTState P V}
    (inv : PBFTInvariant primary f F st) {i : P} (hiF : i ∉ F) {r' : ReplicaState P V}
    {net' : Finset (PBFTMsg P V)} (hsub : st.network ⊆ net')
    (hview : (st.replicas i).view ≤ r'.view)
    (heff : (st.replicas i).effectiveView ≤ r'.effectiveView)
    (hacc : (st.replicas i).accepted ⊆ r'.accepted)
    (hcerts : (st.replicas i).preparedCerts ⊆ r'.preparedCerts)
    (h_view_le : r'.view ≤ r'.effectiveView)
    (h_active : r'.view ≠ (st.replicas i).view →
      ∃ vset oset, NewViewValidIn primary f net' r'.view vset oset ∧
        ∀ prop ∈ oset, ⟨r'.view, prop.slot, prop.val⟩ ∈ r'.accepted)
    (h_acc_view : ∀ e ∈ r'.accepted, e ∉ (st.replicas i).accepted → e.view ≤ r'.view)
    (h_acc_unique : ∀ e₁ ∈ r'.accepted, e₁ ∉ (st.replicas i).accepted → ∀ e₂ ∈ r'.accepted,
      e₁.view = e₂.view → e₁.slot = e₂.slot → e₁.val = e₂.val)
    (h_acc_pos : ∀ e ∈ r'.accepted, e ∉ (st.replicas i).accepted → 0 < e.view →
      ∃ vset oset, NewViewValidIn primary f net' e.view vset oset ∧
        ∀ prop ∈ oset, prop.slot = e.slot → e.val = prop.val)
    (h_cert : ∀ c ∈ r'.preparedCerts, c ∉ (st.replicas i).preparedCerts →
      c.ValidIn primary f net' ∧ c.view ≤ r'.effectiveView)
    (h_committed : ∀ e ∈ r'.committed, e ∉ (st.replicas i).committed →
      ∃ (c : PreparedCert P V) (committers : Finset P),
        c.view = e.view ∧ c.slot = e.slot ∧ c.val = e.val ∧
        c.ValidIn primary f net' ∧ pbftQuorumSize P f ≤ committers.card ∧
        ∀ q ∈ committers, PBFTMsg.commit e.view e.slot e.val q ∈ net')
    (h_msg : ∀ m ∈ net', m ∉ st.network →
      m.signer primary = i ∧ FreshMsgOK (st.replicas i) r' i net' m) :
    PBFTInvariant primary f F ⟨net', Function.update st.replicas i r'⟩ where
  view_le_effective j hjF := by
    rcases eq_or_ne j i with rfl | hj
    · simpa only [Function.update_self] using h_view_le
    · simpa only [Function.update_of_ne hj] using inv.view_le_effective j hjF
  accepted_view_le j hjF e he := by
    rcases mem_update_replica ReplicaState.accepted he with he | ⟨rfl, he, hnew⟩
    · exact (inv.accepted_view_le j hjF e he).trans (le_update_replica ReplicaState.view hview j)
    · simpa only [Function.update_self] using h_acc_view e he hnew
  accepted_unique j hjF e₁ he₁ e₂ he₂ hv hs := by
    rcases mem_update_replica ReplicaState.accepted he₁ with ho₁ | ⟨rfl, hn₁, hnew₁⟩
    · rcases mem_update_replica ReplicaState.accepted he₂ with ho₂ | ⟨rfl, hn₂, hnew₂⟩
      · exact inv.accepted_unique j hjF e₁ ho₁ e₂ ho₂ hv hs
      · exact (h_acc_unique e₂ hn₂ hnew₂ e₁ (hacc ho₁) hv.symm hs.symm).symm
    · simp only [Function.update_self] at he₂
      exact h_acc_unique e₁ hn₁ hnew₁ e₂ he₂ hv hs
  voted_imp_accepted j hjF v s val hv := by
    have hvote : HonestVoted primary st j v s val ∨ j = i ∧ ⟨v, s, val⟩ ∈ r'.accepted := by
      rcases hv with ⟨hj, hm⟩ | ⟨hj, hm⟩
      · by_cases hold : PBFTMsg.prePrepare v s val ∈ st.network
        · exact Or.inl (Or.inl ⟨hj, hold⟩)
        · exact Or.inr ⟨hj.trans (h_msg _ hm hold).1, (h_msg _ hm hold).2⟩
      · by_cases hold : PBFTMsg.prepare v s val j ∈ st.network
        · exact Or.inl (Or.inr ⟨hj, hold⟩)
        · exact Or.inr (h_msg _ hm hold)
    rcases hvote with hvote | ⟨rfl, hnew⟩
    · exact le_update_replica ReplicaState.accepted hacc j
        (inv.voted_imp_accepted j hjF v s val hvote)
    · simpa only [Function.update_self] using hnew
  active_pos_newView j hjF hpos := by
    rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self] at hpos ⊢
      by_cases hv : r'.view = (st.replicas j).view
      · rw [hv] at hpos ⊢
        obtain ⟨vset, oset, hnv, hprop⟩ := inv.active_pos_newView j hjF hpos
        exact ⟨vset, oset, hnv.mono hsub, fun prop hp => hacc (hprop prop hp)⟩
      · exact h_active hv
    · simp only [Function.update_of_ne hj] at hpos ⊢
      obtain ⟨vset, oset, hnv, hprop⟩ := inv.active_pos_newView j hjF hpos
      exact ⟨vset, oset, hnv.mono hsub, hprop⟩
  accepted_pos_newView j hjF e he hpos := by
    rcases mem_update_replica ReplicaState.accepted he with he | ⟨rfl, he, hnew⟩
    · obtain ⟨vset, oset, hnv, hprop⟩ := inv.accepted_pos_newView j hjF e he hpos
      exact ⟨vset, oset, hnv.mono hsub, hprop⟩
    · exact h_acc_pos e he hnew hpos
  prepared_valid j hjF c hc := by
    rcases mem_update_replica ReplicaState.preparedCerts hc with hc | ⟨rfl, hc, hnew⟩
    · obtain ⟨hval, hle⟩ := inv.prepared_valid j hjF c hc
      exact ⟨hval.mono hsub, hle.trans (le_update_replica ReplicaState.effectiveView heff j)⟩
    · simpa only [Function.update_self] using h_cert c hc hnew
  commit_has_cert k hkF v s val hm := by
    by_cases hold : PBFTMsg.commit v s val k ∈ st.network
    · obtain ⟨hle, c, hc, hcv⟩ := inv.commit_has_cert k hkF v s val hold
      exact ⟨hle.trans (le_update_replica ReplicaState.effectiveView heff k),
        c, le_update_replica ReplicaState.preparedCerts hcerts k hc, hcv⟩
    · obtain ⟨hsig, -, hok⟩ := h_msg _ hm hold
      simp only [PBFTMsg.signer] at hsig
      subst hsig
      simpa only [Function.update_self] using hok
  viewChange_le_effective vc hvcF hm := by
    by_cases hold : PBFTMsg.viewChange vc ∈ st.network
    · exact (inv.viewChange_le_effective vc hvcF hold).trans
        (le_update_replica ReplicaState.effectiveView heff vc.sender)
    · obtain ⟨hsig, hok, -⟩ := h_msg _ hm hold
      simp only [PBFTMsg.signer] at hsig
      simpa only [hsig, Function.update_self] using hok
  viewChange_contains_commit vc hvcF hm v s val hcm hlt := by
    by_cases hold : PBFTMsg.viewChange vc ∈ st.network
    · by_cases hcold : PBFTMsg.commit v s val vc.sender ∈ st.network
      · exact inv.viewChange_contains_commit vc hvcF hold v s val hcold hlt
      · obtain ⟨hsig, hle, -⟩ := h_msg _ hcm hcold
        simp only [PBFTMsg.signer] at hsig
        have := inv.viewChange_le_effective vc hvcF hold
        rw [hsig] at this
        omega
    · obtain ⟨hsig, -, hok⟩ := h_msg _ hm hold
      simp only [PBFTMsg.signer] at hsig
      exact hok v s val (hsig ▸ hcm) hlt
  committed_witness j hjF e he := by
    rcases mem_update_replica ReplicaState.committed he with he | ⟨rfl, he, hnew⟩
    · obtain ⟨c, comms, hv, hs, hval, hc, hcard, hcm⟩ := inv.committed_witness j hjF e he
      exact ⟨c, comms, hv, hs, hval, hc.mono hsub, hcard, fun q hq => hsub (hcm q hq)⟩
    · exact h_committed e he hnew

/-- Replica `i` accepts the entry `⟨v, s, val⟩` at a slot still free in its current view `v` and
sends the message `m`, a vote for it (`propose`, `acceptPrePrepare`). -/
private lemma PBFTInvariant.of_accept {st : PBFTState P V} (inv : PBFTInvariant primary f F st)
    {i : P} (hiF : i ∉ F) {v s : ℕ} {val : Option V} (hv : (st.replicas i).view = v)
    (hfresh : ∀ e ∈ (st.replicas i).accepted, e.view = v → e.slot = s → False)
    {m : PBFTMsg P V} (hm : m.signer primary = i)
    (hmok : FreshMsgOK (st.replicas i)
      { st.replicas i with accepted := insert ⟨v, s, val⟩ (st.replicas i).accepted } i
      (insert m st.network) m) :
    PBFTInvariant primary f F ⟨insert m st.network, Function.update st.replicas i
      { st.replicas i with accepted := insert ⟨v, s, val⟩ (st.replicas i).accepted }⟩ := by
  refine inv.of_replica_update hiF (Finset.subset_insert _ _) le_rfl le_rfl
    (Finset.subset_insert _ _) subset_rfl (inv.view_le_effective _ hiF)
    (absurd rfl) (fun e he hn => ?_) (fun e₁ he₁ hn e₂ he₂ hv hs => ?_)
    (fun e he hn hpos => ?_) (fun _ => absurd) (fun _ => absurd)
    (fun m' hm' hn => ?_)
  · rw [Finset.eq_of_mem_insert_of_notMem he hn]; exact hv.ge
  · obtain rfl := Finset.eq_of_mem_insert_of_notMem he₁ hn
    rcases Finset.mem_insert.mp he₂ with rfl | he₂
    · rfl
    · exact (hfresh e₂ he₂ hv.symm hs.symm).elim
  · obtain rfl := Finset.eq_of_mem_insert_of_notMem he hn
    obtain ⟨vset, oset, hnv, hacc⟩ := inv.active_pos_newView _ hiF (by rw [hv]; exact hpos)
    rw [hv] at hnv hacc
    exact ⟨vset, oset, hnv.mono (Finset.subset_insert _ _),
      fun prop hp hs => (hfresh _ (hacc prop hp) rfl hs).elim⟩
  · obtain rfl := Finset.eq_of_mem_insert_of_notMem hm' hn
    exact ⟨hm, hmok⟩

/-- Replica `i` enters view `v'` on the valid `NEW-VIEW(v', vset, oset)` and accepts the proposals
`oset` (`formNewView`, `enterNewView`). -/
private lemma PBFTInvariant.of_enter_view {st : PBFTState P V}
    (inv : PBFTInvariant primary f F st) {i : P} (hiF : i ∉ F) {v' : ℕ}
    {vset : Finset (ViewChangeMsg P V)} {oset : Finset (SlotProposal V)}
    {net' : Finset (PBFTMsg P V)} (hsub : st.network ⊆ net') (hview : (st.replicas i).view < v')
    (heff : (st.replicas i).effectiveView ≤ v') (hnv : NewViewValidIn primary f net' v' vset oset)
    (h_msg : ∀ m ∈ net', m ∉ st.network → m.signer primary = i ∧
      FreshMsgOK (st.replicas i)
        { st.replicas i with
          view := v', inViewChange := false, targetView := v'
          accepted := (st.replicas i).accepted ∪ oset.image fun prop => ⟨v', prop.slot, prop.val⟩ }
        i net' m) :
    PBFTInvariant primary f F ⟨net', Function.update st.replicas i
      { st.replicas i with
        view := v', inViewChange := false, targetView := v'
        accepted := (st.replicas i).accepted ∪
          oset.image fun prop => ⟨v', prop.slot, prop.val⟩ }⟩ := by
  have hoset := hnv.2.2.2.2.2
  refine inv.of_replica_update hiF hsub hview.le heff Finset.subset_union_left subset_rfl le_rfl
    (fun _ => ⟨vset, oset, hnv, fun _ hp => ?_⟩) (fun e he hn => ?_)
    (fun e₁ he₁ hn e₂ he₂ hv hs => ?_) (fun e he hn _ => ?_) (fun _ => absurd) (fun _ => absurd)
    h_msg
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  · obtain ⟨prop, _, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp he).resolve_left hn)
    exact le_rfl
  · obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp he₁).resolve_left hn)
    rcases Finset.mem_union.mp he₂ with he₂ | he₂
    · have := inv.accepted_view_le _ hiF e₂ he₂
      dsimp only at hv
      omega
    · obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp he₂
      exact computeOset_slot_unique hoset hp₁ hp₂ hs
  · obtain ⟨prop₀, hp₀, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp he).resolve_left hn)
    exact ⟨vset, oset, hnv, fun prop hp hs => computeOset_slot_unique hoset hp₀ hp hs.symm⟩

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
    · obtain ⟨hpF, hpv, -, hfresh⟩ := hg
      rw [filter_accepted_eq_empty_iff] at hfresh
      exact inv.of_accept hpF hpv hfresh rfl (Finset.mem_insert_self _ _)
    · exact inv
  | acceptPrePrepare i₀ v s val =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, -, hi₀v, -, -, hfresh⟩ := hg
      rw [filter_accepted_eq_empty_iff] at hfresh
      exact inv.of_accept hi₀F hi₀v hfresh rfl (Finset.mem_insert_self _ _)
    · exact inv
  | completePrepare i₀ c₀ =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, hi₀v, hi₀in, -, hc₀val⟩ := hg
      have heff_eq : (st.replicas i₀).effectiveView = c₀.view := by
        simp only [ReplicaState.effectiveView, hi₀in, Bool.false_eq_true, ↓reduceIte, hi₀v]
      refine inv.of_replica_update hi₀F (Finset.subset_insert _ _) le_rfl le_rfl subset_rfl
        (Finset.subset_insert _ _) (inv.view_le_effective _ hi₀F) (absurd rfl)
        (fun _ => absurd) (fun _ => absurd) (fun _ => absurd) (fun _ => absurd)
        (h_cert := fun c hc hn => ?_) (h_msg := fun m hm hn => ?_)
      · obtain rfl := Finset.eq_of_mem_insert_of_notMem hc hn
        exact ⟨hc₀val.mono (Finset.subset_insert _ _), heff_eq.ge⟩
      · obtain rfl := Finset.eq_of_mem_insert_of_notMem hm hn
        exact ⟨rfl, heff_eq.le, heff_eq.ge, c₀, Finset.mem_insert_self _ _, rfl, rfl, rfl⟩
    · exact inv
  | completeCommit i₀ c₀ committers =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, -, -, hc₀mem, hcard, hcm_all⟩ := hg
      refine inv.of_replica_update hi₀F subset_rfl le_rfl le_rfl subset_rfl subset_rfl
        (inv.view_le_effective _ hi₀F) (absurd rfl) (fun _ => absurd) (fun _ => absurd)
        (fun _ => absurd) (fun _ => absurd) (fun _ => absurd) (h_committed := fun e he hn => ?_)
      obtain rfl := Finset.eq_of_mem_insert_of_notMem he hn
      exact ⟨c₀, committers, rfl, rfl, rfl, (inv.prepared_valid i₀ hi₀F c₀ hc₀mem).1, hcard,
        hcm_all⟩
    · exact inv
  | startViewChange i₀ v' =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, heff_lt⟩ := hg
      refine inv.of_replica_update hi₀F (Finset.subset_insert _ _) le_rfl heff_lt.le subset_rfl
        subset_rfl ((inv.view_le_effective _ hi₀F).trans heff_lt.le)
        (absurd rfl) (fun _ => absurd) (fun _ => absurd) (fun _ => absurd) (fun _ => absurd)
        (fun _ => absurd) (h_msg := fun m hm hn => ?_)
      obtain rfl := Finset.eq_of_mem_insert_of_notMem hm hn
      refine ⟨rfl, le_rfl, fun v s val hcm _ => ?_⟩
      obtain ⟨-, c, hc, hcv⟩ :=
        inv.commit_has_cert i₀ hi₀F v s val (Finset.mem_of_mem_insert_of_ne hcm nofun)
      exact ⟨c, hc, hcv⟩
    · exact inv
  | formNewView v' vset =>
    unfold pbftStep; dsimp only
    cases hoset : computeOset vset with
    | none => exact inv
    | some oset =>
      dsimp only
      split_ifs with hg
      · obtain ⟨hpF, hv'pos, hview_lt, heff_le, hvc_all, hvc_card⟩ := hg
        let net' := insert (PBFTMsg.newView v' vset oset)
          (st.network ∪ oset.image fun prop => PBFTMsg.prePrepare v' prop.slot prop.val)
        have hsub : st.network ⊆ net' := Finset.subset_union_left.trans (Finset.subset_insert _ _)
        refine inv.of_enter_view hpF hsub hview_lt heff_le
          ⟨hv'pos, Finset.mem_insert_self _ _, fun prop hp => ?_,
            fun vc hvc => ⟨(hvc_all vc hvc).1, (hvc_all vc hvc).2.mono hsub⟩, hvc_card, hoset⟩
          fun m hm hn => ?_
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact ⟨rfl, trivial⟩
          obtain ⟨prop, hp, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hm).resolve_left hn)
          exact ⟨rfl, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
      · exact inv
  | enterNewView i₀ v' vset oset =>
    unfold pbftStep; dsimp only
    split_ifs with hg
    · obtain ⟨hi₀F, -, hview_lt, heff_le, hnv⟩ := hg
      refine inv.of_enter_view hi₀F Finset.subset_union_left hview_lt heff_le
        (hnv.mono Finset.subset_union_left) fun m hm hn => ?_
      obtain ⟨prop, hp, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hm).resolve_left hn)
      exact ⟨rfl, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
    · exact inv
  | byzSend m =>
    unfold pbftStep; dsimp only
    split_ifs with hmF
    · have hsub : st.network ⊆ insert m st.network := Finset.subset_insert _ _
      have hold : ∀ m' ∈ insert m st.network, m'.signer primary ∉ F → m' ∈ st.network :=
        fun m' h hs => (Finset.mem_insert.1 h).resolve_left (by rintro rfl; exact hs hmF)
      refine
        { inv with
          voted_imp_accepted := fun i hiF v₀ s₀ val₀ hv =>
            inv.voted_imp_accepted i hiF v₀ s₀ val₀ <|
              hv.imp (fun ⟨hi, hm'⟩ => ⟨hi, hold _ hm' (show primary v₀ ∉ F from hi ▸ hiF)⟩)
                fun ⟨hi, hm'⟩ => ⟨hi, hold _ hm' hiF⟩
          active_pos_newView := fun i hiF hpos =>
            let ⟨vs, os, hnv, hacc⟩ := inv.active_pos_newView i hiF hpos
            ⟨vs, os, hnv.mono hsub, hacc⟩
          accepted_pos_newView := fun i hiF e he hpos =>
            let ⟨vs, os, hnv, hprop⟩ := inv.accepted_pos_newView i hiF e he hpos
            ⟨vs, os, hnv.mono hsub, hprop⟩
          prepared_valid := fun i hiF c hc =>
            (inv.prepared_valid i hiF c hc).imp_left (·.mono hsub)
          commit_has_cert := fun k hkF v₀ s₀ val₀ hm' =>
            inv.commit_has_cert k hkF v₀ s₀ val₀ (hold _ hm' hkF)
          viewChange_le_effective := fun vc hvcF hm' =>
            inv.viewChange_le_effective vc hvcF (hold _ hm' hvcF)
          viewChange_contains_commit := fun vc hvcF hm' v₀ s₀ val₀ hcm hlt =>
            inv.viewChange_contains_commit vc hvcF (hold _ hm' hvcF) v₀ s₀ val₀ (hold _ hcm hvcF)
              hlt
          committed_witness := fun i hiF e he =>
            let ⟨c, comms, hv, hs, hval, hc, hcard, hcm⟩ := inv.committed_witness i hiF e he
            ⟨c, comms, hv, hs, hval, hc.mono hsub, hcard, fun q hq => hsub (hcm q hq)⟩ }
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
    -- Honest voter `m ∉ F` in `c'.voters` accepted `(v', s, c'.val)` via a valid `NewView`.
    have hmem_c' := mem_thresholdQuorums_iff.mpr hc'valid.2.2.2
    obtain ⟨m, hm⟩ := hdissem.2 _ hmem_c' _ hmem_c' F hF
    rw [Finset.mem_sdiff, Finset.mem_inter] at hm
    have hm_acc := inv.voted_imp_accepted m hm.2 c'.view c'.slot c'.val
      (hc'valid.voter_honestVoted hm.1.1)
    rw [hc'v, hc's] at hm_acc
    obtain ⟨vset, oset, hnv, hoset_match⟩ :=
      inv.accepted_pos_newView m hm.2 _ hm_acc ((Nat.zero_le v).trans_lt hvlt)
    dsimp only at hnv hoset_match
    -- Quorum intersection between `committers` and `vset` senders yields an honest `k ∉ F`.
    obtain ⟨k, hk⟩ := hdissem.2 _ (mem_thresholdQuorums_iff.mpr hcomm_card) _
      (mem_thresholdQuorums_iff.mpr hnv.2.2.2.2.1) F hF
    rw [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_image] at hk
    obtain ⟨⟨hk_comm, vc_k, hvc_k_mem, rfl⟩, hkF⟩ := hk
    obtain ⟨hvc_k_view, hvc_k_val⟩ := hnv.2.2.2.1 vc_k hvc_k_mem
    obtain ⟨c_k, hc_k_pset, hc_k_v, hc_k_s, -⟩ := inv.viewChange_contains_commit vc_k hkF
      hvc_k_val.2.1 v s val (hcomm_msgs _ hk_comm) (hvc_k_view ▸ hvlt)
    -- Inspect `computeOset vset = some oset` at slot `s`: `c_k` witnesses `s ≤ maxS` and
    -- non-empty `sc`.
    let certs := vset.biUnion ViewChangeMsg.pset
    have hc_k_certs : c_k ∈ certs := Finset.mem_biUnion.mpr ⟨vc_k, hvc_k_mem, hc_k_pset⟩
    have hoset_eq := hnv.2.2.2.2.2
    unfold computeOset at hoset_eq
    dsimp only at hoset_eq
    split_ifs at hoset_eq with hne_certs hall
    swap
    · exact absurd ⟨c_k, hc_k_certs⟩ hne_certs
    injection hoset_eq with hoset_def
    have hs_in_slots :
        s ∈ Finset.range ((certs.image PreparedCert.slot).max' (hne_certs.image _) + 1) :=
      Finset.mem_range.mpr <| Nat.lt_succ_of_le <|
        hc_k_s ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem _ hc_k_certs)
    obtain ⟨o_s, ho_s⟩ := Option.isSome_iff_exists.mp (hall s hs_in_slots)
    have hc'val_eq : c'.val = o_s := hoset_match ⟨s, o_s⟩ (by
      rw [← hoset_def, Finset.mem_biUnion]
      exact ⟨s, hs_in_slots, by rw [ho_s]; exact Finset.mem_singleton_self _⟩) rfl
    -- Unpack `computeSlotVal certs s = some o_s` to find a max-view certificate `c_max`.
    have hc_k_sc : c_k ∈ certs.filter fun c => c.slot = s :=
      Finset.mem_filter.mpr ⟨hc_k_certs, hc_k_s⟩
    unfold computeSlotVal at ho_s
    dsimp only at ho_s
    split_ifs at ho_s with hsc_eq hcard1
    · exact absurd hsc_eq (Finset.ne_empty_iff_nonempty.mpr ⟨c_k, hc_k_sc⟩)
    injection ho_s with ho_s_eq
    generalize_proofs hp at ho_s_eq
    have hspec := (Finset.choose_spec (fun _ => True) _ hp).1
    rw [ho_s_eq, Finset.mem_image] at hspec
    obtain ⟨c_max, hc_max_top, hc_max_val⟩ := hspec
    obtain ⟨hc_max_sc, hc_max_ge⟩ := Finset.mem_filter.mp hc_max_top
    obtain ⟨hc_max_certs, hc_max_s⟩ := Finset.mem_filter.mp hc_max_sc
    obtain ⟨vc_m, hvc_m_mem, hc_max_pset⟩ := Finset.mem_biUnion.mp hc_max_certs
    obtain ⟨hvc_m_view, hvc_m_val⟩ := hnv.2.2.2.1 vc_m hvc_m_mem
    obtain ⟨hc_max_lt, hc_max_valid⟩ := hvc_m_val.2.2 c_max hc_max_pset
    exact hc'val_eq.trans <| hc_max_val.symm.trans <| ih c_max.view (hvc_m_view ▸ hc_max_lt)
      (hc_k_v ▸ hc_max_ge c_k hc_k_sc) hc_max_valid rfl hc_max_s

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

/-- Running the steps `act j` of the replicas `j` of a duplicate-free list `l` in order: if the
step of a ready replica `j` (`R`) grows the network, changes only replica `j` and leaves it done
(`Q`), and readiness and being done survive the network growing, then afterwards every `j ∈ l` is
done and every other replica is unchanged. -/
private lemma foldl_perReplica {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {primary : ℕ → P} {f : ℕ} {F : Finset P} (act : P → PBFTAction P V)
    (R Q : P → Finset (PBFTMsg P V) → ReplicaState P V → Prop)
    (hmono : ∀ j net net' r, net ⊆ net' → (R j net r → R j net' r) ∧ (Q j net r → Q j net' r))
    {l : List P} (hl : l.Nodup)
    (hstep : ∀ j ∈ l, ∀ st : PBFTState P V, R j st.network (st.replicas j) →
      let st' := pbftStep primary f F st (act j)
      st.network ⊆ st'.network ∧ (∀ k ≠ j, st'.replicas k = st.replicas k) ∧
        Q j st'.network (st'.replicas j))
    (st : PBFTState P V) (hR : ∀ j ∈ l, R j st.network (st.replicas j)) :
    let st' := (l.map act).foldl (pbftStep primary f F) st
    st.network ⊆ st'.network ∧ (∀ j ∈ l, Q j st'.network (st'.replicas j)) ∧
      ∀ k ∉ l, st'.replicas k = st.replicas k := by
  induction l generalizing st with
  | nil => exact ⟨Subset.rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | cons b l ih =>
    simp only [List.map_cons, List.foldl_cons]
    obtain ⟨hb, hl⟩ := List.nodup_cons.1 hl
    obtain ⟨hsub, hrep, hQ⟩ := hstep b List.mem_cons_self st (hR b List.mem_cons_self)
    obtain ⟨hsub', hQ', hrep'⟩ := ih hl (fun j hj => hstep j (.tail _ hj)) _ fun j hj => by
      rw [hrep j fun h => hb (h ▸ hj)]
      exact (hmono j _ _ _ hsub).1 (hR j (.tail _ hj))
    refine ⟨hsub.trans hsub', fun j hj => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · rw [hrep' j hb]; exact (hmono j _ _ _ hsub').2 hQ
      · exact hQ' j hj
    · rw [hrep' k (List.not_mem_of_not_mem_cons hk), hrep k (List.ne_of_not_mem_cons hk)]

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
  have hst₁_eq : st₁ =
      { network := insert (PBFTMsg.prePrepare v s val) st.network
        replicas := Function.update st.replicas (primary v)
          { st.replicas (primary v) with
            accepted := insert ⟨v, s, val⟩ (st.replicas (primary v)).accepted } } := by
    unfold st₁ pbftStep; dsimp only
    simp only [hp_honest, not_false_eq_true, hp_v, hp_in,
      filter_accepted_eq_empty_iff.mpr (hfresh (primary v) hp_honest), and_self, ↓reduceIte]
  -- Phase 1b: all honest backups accept `PrePrepare` and emit `Prepare`.
  have hbs_mem : ∀ j ∈ backupList, j ∉ F ∧ j ≠ primary v := fun j hj =>
    of_decide_eq_true (List.mem_filter.mp hj).2
  have hpre₁ : PBFTMsg.prePrepare v s val ∈ st₁.network := by
    rw [hst₁_eq]; exact Finset.mem_insert_self _ _
  obtain ⟨hnet₁₂, hbs_post, hp_unchanged⟩ :=
    foldl_perReplica (primary := primary) (f := f) (F := F)
      (fun j => PBFTAction.acceptPrePrepare j v s val)
      (fun _ net r => PBFTMsg.prePrepare v s val ∈ net ∧ r.view = v ∧ r.inViewChange = false ∧
        ∀ e ∈ r.accepted, e.view = v → e.slot = s → False)
      (fun j net r => PBFTMsg.prepare v s val j ∈ net ∧ ⟨v, s, val⟩ ∈ r.accepted ∧ r.view = v ∧
        r.inViewChange = false)
      (fun _ _ _ _ hsub => ⟨fun h => ⟨hsub h.1, h.2⟩, fun h => ⟨hsub h.1, h.2⟩⟩) (hnodup.filter _)
      (fun j hj st ⟨hpre, hv, hin, hfresh⟩ => by
        unfold pbftStep; dsimp only
        split_ifs with hg
        · simp only [Function.update_self]
          exact ⟨Finset.subset_insert _ _, fun k hk => Function.update_of_ne hk _ _,
            Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, hv, hin⟩
        · exact absurd ⟨(hbs_mem j hj).1, (hbs_mem j hj).2, hv, hin, hpre,
            filter_accepted_eq_empty_iff.mpr hfresh⟩ hg)
      st₁ fun j hj => by
        obtain ⟨hjF, hjne⟩ := hbs_mem j hj
        have hrep : st₁.replicas j = st.replicas j := by
          rw [hst₁_eq]; exact Function.update_of_ne hjne _ _
        rw [hrep]
        exact ⟨hpre₁, (hactive j hjF).1, (hactive j hjF).2, hfresh j hjF⟩
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
    refine ⟨hnet₁₂ hpre₁, Finset.notMem_erase _ _, fun q hq => ?_, hvoters_eq ▸ hhonest_card⟩
    rw [Finset.mem_erase, Finset.mem_sdiff] at hq
    exact (hbs_post q (List.mem_filter.mpr ⟨hfull q, decide_eq_true ⟨hq.2.2, hq.1⟩⟩)).1
  have hhonest_mem : ∀ i ∈ honestList, i ∉ F := fun i hi =>
    of_decide_eq_true (List.mem_filter.mp hi).2
  have hprep_ready : ∀ i ∈ honestList, (st₂.replicas i).view = cert.view ∧
      (st₂.replicas i).inViewChange = false ∧
      ⟨cert.view, cert.slot, cert.val⟩ ∈ (st₂.replicas i).accepted := by
    intro i hi
    by_cases hip : i = primary v
    · subst hip
      rw [hp_unchanged _ fun hm => (hbs_mem _ hm).2 rfl, hst₁_eq]
      simp only [Function.update_self, Finset.mem_insert, true_or, cert]
      exact ⟨hp_v, hp_in, trivial⟩
    · obtain ⟨_, hacc, hv_i, hin_i⟩ :=
        hbs_post i (List.mem_filter.mpr ⟨hfull i, decide_eq_true ⟨hhonest_mem i hi, hip⟩⟩)
      exact ⟨hv_i, hin_i, hacc⟩
  obtain ⟨-, hprep_post, -⟩ :=
    foldl_perReplica (primary := primary) (f := f) (F := F)
      (fun i => PBFTAction.completePrepare i cert)
      (fun _ net r => cert.ValidIn primary f net ∧ r.view = cert.view ∧ r.inViewChange = false ∧
        ⟨cert.view, cert.slot, cert.val⟩ ∈ r.accepted)
      (fun i net r => PBFTMsg.commit cert.view cert.slot cert.val i ∈ net ∧
        cert ∈ r.preparedCerts ∧ r.view = cert.view ∧ r.inViewChange = false)
      (fun _ _ _ _ hsub => ⟨fun h => ⟨h.1.mono hsub, h.2⟩, fun h => ⟨hsub h.1, h.2⟩⟩)
      (hnodup.filter _)
      (fun i hi st ⟨hc, hv, hin, hacc⟩ => by
        unfold pbftStep; dsimp only
        split_ifs with hg
        · simp only [Function.update_self]
          exact ⟨Finset.subset_insert _ _, fun k hk => Function.update_of_ne hk _ _,
            Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, hv, hin⟩
        · exact absurd ⟨hhonest_mem i hi, hv, hin, hacc, hc⟩ hg)
      st₂ fun i hi => ⟨hcert_valid, hprep_ready i hi⟩
  let st₃ := (honestList.map fun i => PBFTAction.completePrepare i cert).foldl
    (pbftStep primary f F) st₂
  -- Phase 3: all honest replicas observe `honest` commits (`≥ pbftQuorumSize P f`) and commit
  -- locally.
  have hcm_all : ∀ q ∈ honest, PBFTMsg.commit cert.view cert.slot cert.val q ∈ st₃.network :=
    fun q hq => (hprep_post q (List.mem_filter.mpr
      ⟨hfull q, decide_eq_true (Finset.mem_sdiff.mp hq).2⟩)).1
  obtain ⟨-, hcom_post, -⟩ :=
    foldl_perReplica (primary := primary) (f := f) (F := F)
      (fun i => PBFTAction.completeCommit i cert honest)
      (fun _ net r => (∀ q ∈ honest, PBFTMsg.commit cert.view cert.slot cert.val q ∈ net) ∧
        r.view = cert.view ∧ r.inViewChange = false ∧ cert ∈ r.preparedCerts)
      (fun _ _ r => ⟨cert.view, cert.slot, cert.val⟩ ∈ r.committed)
      (fun _ _ _ _ hsub => ⟨fun h => ⟨fun q hq => hsub (h.1 q hq), h.2⟩, id⟩) (hnodup.filter _)
      (fun i hi st ⟨hcm, hv, hin, hc⟩ => by
        unfold pbftStep; dsimp only
        split_ifs with hg
        · simp only [Function.update_self]
          exact ⟨subset_rfl, fun k hk => Function.update_of_ne hk _ _, Finset.mem_insert_self _ _⟩
        · exact absurd ⟨hhonest_mem i hi, hv, hin, hc, hhonest_card, hcm⟩ hg)
      st₃ fun i hi =>
        have ⟨_, hc, hv, hin⟩ := hprep_post i hi
        ⟨hcm_all, hv, hin, hc⟩
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
