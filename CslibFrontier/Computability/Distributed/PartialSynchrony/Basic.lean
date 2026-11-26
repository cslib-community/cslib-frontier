/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup

/-!
# Partial synchrony and unconditional pre-GST quorum-locking safety

Deterministic fault-tolerant consensus in the basic round model of partial synchrony introduced by
[Dwork, Lynch and Stockmeyer, §3.1][DworkLynchStockmeyer1988] (which captures synchronous
processors with communication bound `Δ` holding from an unknown Global Stabilization Time `GST`
onward via [§4.1][DworkLynchStockmeyer1988]).

## Model

A `PartialSyncProtocol P V State Msg` specifies deterministic round-based execution over processes
`P` with initial inputs in `V`, outgoing messages `send`, state transitions `update` taking
per-sender `Option Msg` deliveries, and optional write-once decisions
`output : P → State → Option V`.

Before `GST`, an adversarial network schedule `deliver : ℕ → P → P → Bool` may drop any subset of
point-to-point messages in any round, modeling arbitrary message loss and timeouts prior to
stabilization. `IsGST deliver F gst` asserts that from round `gst` onward, every message between
correct processes (`∉ F`) is delivered in its round. Two fault regimes share the same protocol
interface:

* **Unauthenticated Byzantine faults** (`byzantineState`, `SolvesByzantinePartialSync`): faulty
  processes `j ∈ F` send arbitrary per-recipient messages `adv r j i : Option Msg` (equivocation
  and omission), without cryptographic signatures (receivers know only direct sender identity).
* **Crash and omission faults** (`omissionState`, `SolvesOmissionPartialSync`): all processes
  execute protocol code from their initial values, while `deliver` may omit any message before
  `gst` and any message sent or received by `F` at or after `gst`. Every omission run is a
  special case of a Byzantine run (`omissionState_eq_byzantineState`), so tolerating Byzantine
  faults implies tolerating omission faults (`SolvesByzantinePartialSync.toOmission`).

Crucially, as emphasized in [Dwork, Lynch and Stockmeyer, §1.2, p. 290][DworkLynchStockmeyer1988],
the safety properties (*irrevocability*, *agreement*, and *validity*) hold **unconditionally** for
every `deliver` schedule—even if `GST` never arrives (`GST = ∞`)—while post-`GST` liveness is
established in `CslibFrontier.Computability.Distributed.PartialSynchrony.Liveness`.

## Streamlined view-based quorum-locking protocols vs. [DworkLynchStockmeyer1988] §3.2

In [Dwork, Lynch and Stockmeyer, §§3.2.1–3.2.3][DworkLynchStockmeyer1988], Algorithms 1–3 alternate
trying phases with explicit lock-release phases and piggyback monotone `PROPER` sets on every
message, using a continuous Srikanth–Toueg echo broadcast across all subsequent rounds in the
unauthenticated Byzantine case (Algorithm 3, Figure 1, p. 301). Here we formalize two original
three- and six-subround rotating-coordinator view-based quorum-locking protocols over an arbitrary
`[DecidableEq V]` domain:

* `byzQuorumProtocol` (`3 * t < Fintype.card P`, 6 subrounds per view, unauthenticated channels):
  Subrounds 0–1 perform a two-round raw/certified status and input-properness relay using the
  `t + 1` vs. `n - t` amplification gap so unauthenticated lock certificates (`ViewLock`) and
  proper initial values cannot be forged by `|F| ≤ t` faulty senders yet relay from an honest
  coordinator to all correct voters after `GST`; Subround 2 proposes (`Proposal`); Subround 3 runs
  an `(n - t)` echo/prevote stage (`prevoteQuorum_unique`); Subround 4 runs an `(n - t)` vote
  stage that updates `locked : Option (ViewLock V)`; and Subround 5 runs an `(n - t)` commit stage
  that sets `decided : Option V`.
* `omissionQuorumProtocol` (`2 * t < Fintype.card P`, 3 subrounds per view): Subround 0 reports
  status and current lock, Subround 1 proposes the highest-view reported lock (or coordinator
  input when unlocked) and locks upon compatibility, and Subround 2 decides upon `n - t`
  acknowledgments. Because an omission-faulty process that omits nothing is indistinguishable from
  a correct process, `SolvesOmissionPartialSync` uses DLS's strong unanimity hypothesis
  `∀ i, x i = v` ([§2.4, p. 295][DworkLynchStockmeyer1988]), whereas `byzQuorumProtocol` achieves
  the stronger correct-process validity `∀ i ∉ F, x i = v` for `3 * t < Fintype.card P`.

## Main definitions

* `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol`: deterministic basic-round-model
  consensus protocol.
* `Cslib.Distributed.PartialSynchrony.IsGST`: post-stabilization reliable delivery among correct
  processes.
* `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol.SolvesByzantinePartialSync`,
  `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol.SolvesOmissionPartialSync`: consensus
  specifications under Byzantine and crash/omission faults.
* `Cslib.Distributed.PartialSynchrony.ownInputProtocol`: zero-communication protocol for `|P| ≤ 1`.
* `Cslib.Distributed.PartialSynchrony.ViewLock`, `ProperReport`, `Proposal`: named domain records
  for view locks, input-properness reports, and coordinator proposals.
* `Cslib.Distributed.PartialSynchrony.byzQuorumProtocol`: 6-subround unauthenticated Byzantine
  view-locking protocol (`3 * t < Fintype.card P`).
* `Cslib.Distributed.PartialSynchrony.omissionQuorumProtocol`: 3-subround omission/crash
  view-locking protocol (`2 * t < Fintype.card P`).

## Main results

* `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol.omissionState_eq_byzantineState`,
  `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol.SolvesByzantinePartialSync.toOmission`:
  omission runs embed into Byzantine runs.
* `Cslib.Distributed.PartialSynchrony.solvesByzantinePartialSync_ownInput`: zero-communication
  consensus on at most one process.
* `Cslib.Distributed.PartialSynchrony.quorum_inter_notMem`: two quorums whose cardinalities sum to
  more than `|P| + |F|` share a correct process (`∉ F`).
* `Cslib.Distributed.PartialSynchrony.prevoteQuorum_unique`: within-view `(n - t)` echo/prevote
  quorum uniqueness under `3 * t < Fintype.card P`.
* `Cslib.Distributed.PartialSynchrony.voterCerts_sound`: unforgeability of unauthenticated view
  certificates (`|F| ≤ t`).
* `Cslib.Distributed.PartialSynchrony.byzQuorum_lock_preservation`: once `val₀` is decided in view
  `v₀`, at least `n - 2 * t` correct processes hold locks on `val₀` at views `≥ v₀` across all
  higher views and no correct process ever Stage-2 votes for `val ≠ val₀`.
* `Cslib.Distributed.PartialSynchrony.byzQuorum_irrevocable`, `byzQuorum_agreement`,
  `byzQuorum_validity`: unconditional pre-GST irrevocability, global agreement, and strong
  correct-input validity for `byzQuorumProtocol`.
* `Cslib.Distributed.PartialSynchrony.omission_irrevocable`, `omission_agreement`,
  `omission_validity`: unconditional pre-GST irrevocability, global agreement, and strong unanimity
  for `omissionQuorumProtocol`.

## References

* [C. Dwork, N. Lynch, L. Stockmeyer, *Consensus in the presence of partial
  synchrony*][DworkLynchStockmeyer1988]
-/

public section

namespace Cslib.Distributed.PartialSynchrony

open Finset

/-! ### Partial-synchrony basic round model -/

/-- A deterministic consensus protocol in the basic round model of partial synchrony
[Dwork, Lynch and Stockmeyer, §3.1][DworkLynchStockmeyer1988].

Process `i` starts in `init i (x i)`. In round `r + 1`, each correct process `j` attempts to send
`send r j s i` to `i`; `i` receives `Option Msg` per sender (`none` when omitted by the network or
sender) and transitions via `update r i s recv`. `output i s` is `some v` once `i` has decided `v`
and `none` while undecided. -/
structure PartialSyncProtocol (P V State Msg : Type*) where
  /-- Initial local state of process `i` on input value `v`. -/
  init : P → V → State
  /-- Message sent by process `i` in state `s` to recipient `j` during round `r + 1`. -/
  send : ℕ → P → State → P → Msg
  /-- Next local state of `i` after round `r + 1` given received `P → Option Msg`. -/
  update : ℕ → P → State → (P → Option Msg) → State
  /-- Decision value read from local state (`none` while undecided). -/
  output : P → State → Option V

/-- Global Stabilization Time condition
[Dwork, Lynch and Stockmeyer, §3.1, p. 295][DworkLynchStockmeyer1988]: from round `gst` onward,
every message sent by a correct process `j ∉ F` to a correct process `i ∉ F` is delivered
(`deliver r j i = true`). Prior to `gst`, `deliver` is unconstrained. -/
@[expose] def IsGST {P : Type*} (deliver : ℕ → P → P → Bool) (F : Finset P) (gst : ℕ) : Prop :=
  ∀ r, gst ≤ r → ∀ j ∉ F, ∀ i ∉ F, deliver r j i = true

namespace PartialSyncProtocol

variable {P V S M : Type*} [DecidableEq P] (π : PartialSyncProtocol P V S M)

/-- State of process `i` after `r` rounds under unauthenticated Byzantine faults `F` with network
delivery schedule `deliver`, faulty-sender table `adv`, and initial inputs `x`. -/
@[expose] def byzantineState (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option M) (x : P → V) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (byzantineState F deliver adv x r i)
      (fun j => if j ∈ F then adv r j i
        else if deliver r j i then some (π.send r j (byzantineState F deliver adv x r j) i)
        else none)

/-- Optional decision of process `i` after `r` rounds in a Byzantine partial-synchrony run. -/
@[expose] def byzantineDecision (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option M) (x : P → V) (r : ℕ) (i : P) : Option V :=
  π.output i (π.byzantineState F deliver adv x r i)

/-- State of process `i` after `r` rounds under crash/omission schedule `deliver` and inputs `x`
[Dwork, Lynch and Stockmeyer, §§2.2, 3.1][DworkLynchStockmeyer1988]. Every process executes the
protocol transition function; omitted links deliver `none`. -/
@[expose] def omissionState (deliver : ℕ → P → P → Bool) (x : P → V) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (omissionState deliver x r i)
      (fun j => if deliver r j i then some (π.send r j (omissionState deliver x r j) i) else none)

/-- Optional decision of process `i` after `r` rounds in an omission/crash partial-synchrony run. -/
@[expose] def omissionDecision (deliver : ℕ → P → P → Bool) (x : P → V) (r : ℕ) (i : P) :
    Option V :=
  π.output i (π.omissionState deliver x r i)

/-- Replays the messages of an omission run `deliver` for `F` inside a Byzantine run. -/
@[expose] def omissionAdv (deliver : ℕ → P → P → Bool) (x : P → V) : ℕ → P → P → Option M :=
  fun r j i => if deliver r j i then some (π.send r j (π.omissionState deliver x r j) i) else none

/-- Every omission/crash run coincides with the Byzantine run against `omissionAdv`. -/
theorem omissionState_eq_byzantineState (F : Finset P) (deliver : ℕ → P → P → Bool) (x : P → V) :
    ∀ r i, π.omissionState deliver x r i =
      π.byzantineState F deliver (π.omissionAdv deliver x) x r i
  | 0, _ => rfl
  | r + 1, i => by
    simp only [omissionState, byzantineState, omissionAdv]
    congr 1
    · exact omissionState_eq_byzantineState F deliver x r i
    · funext j
      by_cases hj : j ∈ F <;> by_cases hdel : deliver r j i <;>
        simp [hj, hdel, omissionState_eq_byzantineState F deliver x r j]

/-- `π` solves consensus against at most `t` unauthenticated Byzantine faults under partial
synchrony [Dwork, Lynch and Stockmeyer, §§1.2, 2.4][DworkLynchStockmeyer1988]: safety
(*irrevocability*, *agreement*, and *validity* when all correct inputs equal `v`) holds
unconditionally across all schedules `deliver`, and every correct process eventually decides once
`IsGST deliver F gst` holds. -/
structure SolvesByzantinePartialSync (t : ℕ) : Prop where
  /-- Decisions of correct processes are write-once. -/
  irrevocable : ∀ F : Finset P, F.card ≤ t → ∀ deliver adv x r₁ r₂, r₁ ≤ r₂ →
    ∀ i ∉ F, ∀ v, π.byzantineDecision F deliver adv x r₁ i = some v →
      π.byzantineDecision F deliver adv x r₂ i = some v
  /-- Unconditional agreement: no two correct processes ever decide distinct values, even without
  `GST`. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ deliver adv x r₁ r₂,
    ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
      π.byzantineDecision F deliver adv x r₁ i = some v₁ →
      π.byzantineDecision F deliver adv x r₂ j = some v₂ → v₁ = v₂
  /-- Unconditional strong validity: if all correct processes start with `v`, no correct process
  ever decides any value other than `v`. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ deliver adv x v,
    (∀ i ∉ F, x i = v) → ∀ r, ∀ i ∉ F, ∀ w,
      π.byzantineDecision F deliver adv x r i = some w → w = v
  /-- Post-GST termination: if `IsGST deliver F gst` holds, every correct process decides. -/
  termination : ∀ F : Finset P, F.card ≤ t → ∀ deliver gst adv x,
    IsGST deliver F gst → ∀ i ∉ F, ∃ r, (π.byzantineDecision F deliver adv x r i).isSome = true

/-- `π` solves consensus against at most `t` crash/omission faults under partial synchrony
[Dwork, Lynch and Stockmeyer, §§2.4, 3.2.1][DworkLynchStockmeyer1988]. Strong unanimity assumes
`∀ i, x i = v` because an omission-faulty process that omits no messages behaves identically to a
correct process. -/
structure SolvesOmissionPartialSync (t : ℕ) : Prop where
  /-- Decisions are write-once. -/
  irrevocable : ∀ deliver x r₁ r₂, r₁ ≤ r₂ → ∀ i v,
    π.omissionDecision deliver x r₁ i = some v → π.omissionDecision deliver x r₂ i = some v
  /-- Unconditional agreement across correct processes and rounds, even without `GST`. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ deliver x r₁ r₂,
    ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
      π.omissionDecision deliver x r₁ i = some v₁ →
      π.omissionDecision deliver x r₂ j = some v₂ → v₁ = v₂
  /-- Unconditional strong unanimity: if all initial values equal `v`, only `v` can be decided. -/
  validity : ∀ deliver x v, (∀ i, x i = v) → ∀ r i w,
    π.omissionDecision deliver x r i = some w → w = v
  /-- Post-GST termination: once `IsGST deliver F gst` holds, every correct process decides. -/
  termination : ∀ F : Finset P, F.card ≤ t → ∀ deliver gst x,
    IsGST deliver F gst → ∀ i ∉ F, ∃ r, (π.omissionDecision deliver x r i).isSome = true

/-- Any protocol solving unauthenticated Byzantine partial-synchrony consensus against `t` faults
also solves omission/crash partial-synchrony consensus against `t` faults. -/
theorem SolvesByzantinePartialSync.toOmission {π : PartialSyncProtocol P V S M} {t : ℕ}
    (h : π.SolvesByzantinePartialSync t) : π.SolvesOmissionPartialSync t where
  irrevocable deliver x r₁ r₂ hr i v hdec := by
    simp only [omissionDecision, π.omissionState_eq_byzantineState ∅] at hdec ⊢
    exact h.irrevocable ∅ (Nat.zero_le t) deliver _ x r₁ r₂ hr i (Finset.notMem_empty i) v hdec
  agreement F hF deliver x r₁ r₂ i hi j hj v₁ v₂ h₁ h₂ := by
    simp only [omissionDecision, π.omissionState_eq_byzantineState F] at h₁ h₂
    exact h.agreement F hF deliver _ x r₁ r₂ i hi j hj v₁ v₂ h₁ h₂
  validity deliver x v hv r i w hdec := by
    simp only [omissionDecision, π.omissionState_eq_byzantineState ∅] at hdec
    exact h.validity ∅ (Nat.zero_le t) deliver _ x v (fun j _ => hv j) r i
      (Finset.notMem_empty i) w hdec
  termination F hF deliver gst x hgst i hi := by
    obtain ⟨r, hr⟩ := h.termination F hF deliver gst (π.omissionAdv deliver x) x hgst i hi
    exact ⟨r, by simpa only [omissionDecision, byzantineDecision,
      ← π.omissionState_eq_byzantineState F deliver x r i] using hr⟩

end PartialSyncProtocol

/-- Zero-communication protocol in which every process immediately decides its own initial input. -/
@[expose] def ownInputProtocol.{u, v} (P : Type u) (V : Type v) :
    PartialSyncProtocol P V V PUnit.{v + 1} where
  init _ v := v
  send _ _ _ _ := PUnit.unit
  update _ _ s _ := s
  output _ s := some s

private theorem ownInputProtocol_byzantineState.{u, v} {P : Type u} {V : Type v} [DecidableEq P]
    (F : Finset P) (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option PUnit.{v + 1})
    (x : P → V) :
    ∀ r i, (ownInputProtocol P V).byzantineState F deliver adv x r i = x i
  | 0, _ => rfl
  | r + 1, i => ownInputProtocol_byzantineState F deliver adv x r i

/-- On at most one process, `ownInputProtocol` solves Byzantine partial-synchrony consensus for
every fault bound `t`. -/
theorem solvesByzantinePartialSync_ownInput {P V : Type*} [DecidableEq P] [Subsingleton P]
    (t : ℕ) : (ownInputProtocol P V).SolvesByzantinePartialSync t where
  irrevocable F _ deliver adv x r₁ r₂ _ i _ v h₁ := by
    simpa only [PartialSyncProtocol.byzantineDecision, ownInputProtocol_byzantineState] using h₁
  agreement F _ deliver adv x r₁ r₂ i _ j _ v₁ v₂ h₁ h₂ := by
    rw [PartialSyncProtocol.byzantineDecision, ownInputProtocol_byzantineState] at h₁ h₂
    exact Option.some.inj ((Subsingleton.elim i j ▸ h₁).symm.trans h₂)
  validity F _ deliver adv x v hv r i hi w hw := by
    rw [PartialSyncProtocol.byzantineDecision, ownInputProtocol_byzantineState, hv i hi] at hw
    exact (Option.some.inj hw).symm
  termination _ _ _ _ _ _ _ _ _ := ⟨0, rfl⟩

/-! ### Quorum intersection and list-based quorum counting -/

/-- Two finite sets of processes `S₁, S₂` whose cardinalities sum to strictly more than
`Fintype.card P + F.card` intersect in at least one process outside `F`. -/
theorem quorum_inter_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {F S₁ S₂ : Finset P} (h : Fintype.card P + F.card < S₁.card + S₂.card) :
    ∃ p ∈ S₁ ∩ S₂, p ∉ F := by
  have hiu := Finset.card_union_add_card_inter S₁ S₂
  have hu : (S₁ ∪ S₂).card ≤ Fintype.card P := Finset.card_le_univ _
  exact Finset.exists_mem_notMem_of_card_lt_card (by omega)

/-- Counting elements of `procs.dedup` satisfying `p` agrees with `(Finset.univ.filter p).card`
whenever `procs` enumerates every `P`. -/
theorem length_filter_dedup_eq_card {P : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ x : P, x ∈ procs) (p : P → Bool) :
    (procs.dedup.filter p).length = (Finset.univ.filter fun x => p x = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_dedup procs).filter p)]
  exact congrArg Finset.card (Finset.ext fun x => by simp only [List.mem_toFinset,
    List.mem_filter, List.mem_dedup, hprocs x, true_and, Finset.mem_filter, Finset.mem_univ])

/-- When `procs` enumerates `P`, `procs.dedup.length = Fintype.card P`. -/
theorem dedup_length_eq_card {P : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) :
    procs.dedup.length = Fintype.card P := by
  simpa using length_filter_dedup_eq_card hprocs (fun _ => true)

/-- Multiplicity of `some v` across `procs.dedup` in `f : P → Option V`. -/
@[expose] def countVal {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (f : P → Option V) (v : V) : ℕ :=
  (procs.dedup.filter fun j => decide (f j = some v)).length

/-- Returns a value `v` carried by at least `q` distinct senders in `procs.dedup`, if any. -/
@[expose] def findQuorumVal {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (q : ℕ) (f : P → Option V) : Option V :=
  procs.dedup.findSome? fun j =>
    match f j with
    | some v => if q ≤ countVal procs f v then some v else none
    | none => none

theorem countVal_eq_card {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {procs : List P} (hprocs : ∀ x : P, x ∈ procs) (f : P → Option V) (v : V) :
    countVal procs f v = (Finset.univ.filter fun j => f j = some v).card := by
  simp only [countVal, length_filter_dedup_eq_card hprocs, decide_eq_true_eq]

private theorem findQuorumVal_sound {P V : Type*} [DecidableEq P] [DecidableEq V]
    {procs : List P} {q : ℕ} {f : P → Option V} {v : V}
    (h : findQuorumVal procs q f = some v) : q ≤ countVal procs f v := by
  obtain ⟨_, j, _, _, hj, _⟩ := List.findSome?_eq_some_iff.1 h
  rcases hfj : f j with _ | w <;> simp only [hfj, reduceCtorEq] at hj
  split_ifs at hj with hq
  exact Option.some.inj hj ▸ hq

/-- When `Fintype.card P < 2 * q`, at most one value can have `q` senders, so `findQuorumVal`
returns `some v` if and only if at least `q` senders carry `some v`. -/
theorem findQuorumVal_eq_some_iff {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {procs : List P} (hprocs : ∀ x : P, x ∈ procs) {q : ℕ} (hq : Fintype.card P < 2 * q)
    (f : P → Option V) (v : V) :
    findQuorumVal procs q f = some v ↔
      q ≤ (Finset.univ.filter fun j => f j = some v).card := by
  have huniq (v₁ v₂ : V)
      (h₁ : q ≤ (Finset.univ.filter fun j => f j = some v₁).card)
      (h₂ : q ≤ (Finset.univ.filter fun j => f j = some v₂).card) : v₁ = v₂ := by
    obtain ⟨j, hj, -⟩ := quorum_inter_notMem (F := ∅)
      (S₁ := Finset.univ.filter fun j => f j = some v₁)
      (S₂ := Finset.univ.filter fun j => f j = some v₂)
      (by simp only [Finset.card_empty]; omega)
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Option.some.inj (hj.1.symm.trans hj.2)
  refine ⟨fun h => countVal_eq_card hprocs f v ▸ findQuorumVal_sound h, fun hv => ?_⟩
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.1
    (by omega : 0 < (Finset.univ.filter fun j => f j = some v).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀
  have hnone : findQuorumVal procs q f ≠ none := fun hn => by
    have hj := (List.findSome?_eq_none_iff.1 hn) j₀ (List.mem_dedup.2 (hprocs j₀))
    have hcv : q ≤ countVal procs f v := by rwa [countVal_eq_card hprocs]
    simp only [hj₀, hcv, ↓reduceIte, reduceCtorEq] at hj
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hnone
  rw [hw, huniq w v (countVal_eq_card hprocs f w ▸ findQuorumVal_sound hw) hv]

private theorem findQuorumVal_dedup_sub {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {procs : List P} (hprocs : ∀ x : P, x ∈ procs) {t : ℕ}
    (hq : Fintype.card P < 2 * (Fintype.card P - t)) (f : P → Option V) {w : V}
    (h : findQuorumVal procs (procs.dedup.length - t) f = some w) :
    Fintype.card P - t ≤ (Finset.univ.filter fun j => f j = some w).card := by
  rw [dedup_length_eq_card hprocs] at h
  exact (findQuorumVal_eq_some_iff hprocs hq f w).1 h

/-- Within-view `(n - t)` echo/prevote quorum uniqueness: when `3 * t < Fintype.card P` and
`F.card ≤ t`, if every correct process `h ∉ F` sends at most one echo value `honestEcho h` in
view `v`, at most one value `val` can gather `n - t` echoes across any two recipients' views
`m₁, m₂` (even if faulty senders equivocate across recipients). -/
theorem prevoteQuorum_unique {P V : Type*} [Fintype P] [DecidableEq V]
    {F : Finset P} {t : ℕ} (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {honestEcho m₁ m₂ : P → Option V}
    (h₁_honest : ∀ h ∉ F, ∀ w, m₁ h = some w → honestEcho h = some w)
    (h₂_honest : ∀ h ∉ F, ∀ w, m₂ h = some w → honestEcho h = some w)
    {v₁ v₂ : V}
    (hq₁ : Fintype.card P - t ≤ (Finset.univ.filter fun j => m₁ j = some v₁).card)
    (hq₂ : Fintype.card P - t ≤ (Finset.univ.filter fun j => m₂ j = some v₂).card) :
    v₁ = v₂ := by
  classical
  obtain ⟨h, hh, hhF⟩ := quorum_inter_notMem (F := F)
    (S₁ := Finset.univ.filter fun j => m₁ j = some v₁)
    (S₂ := Finset.univ.filter fun j => m₂ j = some v₂) (by omega)
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hh
  exact Option.some.inj ((h₁_honest h hhF v₁ hh.1).symm.trans (h₂_honest h hhF v₂ hh.2))

/-! ### Shared domain structures for view-based quorum locking -/

/-- A view-stamped lock or Stage-2 vote `(view, val)`. -/
structure ViewLock (V : Type*) where
  /-- View index in which the vote or lock was formed. -/
  view : ℕ
  /-- Value voted or locked in `view`. -/
  val : V
  deriving @[expose] DecidableEq

/-- Summary of initial-value properness computed in Subround 0 of a view. -/
structure ProperReport (V : Type*) where
  /-- Set to `true` when at least `2t + 1` initial values were received with at least `t + 1`
  entries distinct from every received value, certifying all of `V` proper. -/
  allProper : Bool
  /-- Initial values received from at least `t + 1` distinct senders. -/
  freqVals : List V
  deriving @[expose] DecidableEq

/-- A coordinator proposal in view `v`, carrying a proposed value and an optional justifying lock
view `certView` (`none` for a fresh unlocked proposal, `some u` for a certified lock at `u < v`). -/
structure Proposal (V : Type*) where
  /-- Proposed consensus value. -/
  val : V
  /-- Justifying certificate view (`none` when unlocked). -/
  certView : Option ℕ
  deriving @[expose] DecidableEq

/-- Selects an entry of maximum `view` from a list of `ViewLock`s, if nonempty. -/
@[expose] def pickMaxLock {V : Type*} : List (ViewLock V) → Option (ViewLock V)
  | [] => none
  | lk :: lks =>
    match pickMaxLock lks with
    | none => some lk
    | some best => if best.view ≤ lk.view then some lk else some best

theorem pickMaxLock_eq_none_iff {V : Type*} {lks : List (ViewLock V)} :
    pickMaxLock lks = none ↔ lks = [] := by
  cases lks with
  | nil => simp only [pickMaxLock]
  | cons lk lks =>
    simp only [pickMaxLock, reduceCtorEq, iff_false]
    split <;> (try split_ifs) <;> simp

theorem pickMaxLock_mem {V : Type*} {lks : List (ViewLock V)} {best : ViewLock V}
    (h : pickMaxLock lks = some best) : best ∈ lks := by
  induction lks generalizing best with
  | nil => cases h
  | cons lk lks ih =>
    simp only [pickMaxLock] at h
    split at h
    · exact Option.some.inj h ▸ List.mem_cons_self
    · next _ hrec =>
      split_ifs at h <;> cases h
      exacts [List.mem_cons_self, List.mem_cons_of_mem lk (ih hrec)]

theorem pickMaxLock_le {V : Type*} {lks : List (ViewLock V)} {best : ViewLock V}
    (h : pickMaxLock lks = some best) : ∀ lk ∈ lks, lk.view ≤ best.view := by
  induction lks generalizing best with
  | nil => simp only [pickMaxLock, reduceCtorEq] at h
  | cons hd tl ih =>
    simp only [pickMaxLock] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    split at h
    · next hrec => cases h; simp [pickMaxLock_eq_none_iff.1 hrec]
    · next _ hrec =>
      have htl := ih hrec
      split_ifs at h with hle <;> cases h
      · exact ⟨le_rfl, fun lk hlk => (htl lk hlk).trans hle⟩
      · exact ⟨by omega, htl⟩

/-! ### Unauthenticated Byzantine 6-subround view-locking protocol (`3 * t < Fintype.card P`) -/

/-- Messages exchanged by `byzQuorumProtocol` across the 6 subrounds of each view `v`. -/
inductive ByzViewMsg (V : Type*) where
  /-- Subround 0: initial value and history of Stage-2 `ViewLock` votes emitted by the sender. -/
  | rawStatus (initVal : V) (votedViews : List (ViewLock V))
  /-- Subround 1: amplified properness report and `(t + 1)`-witnessed past `ViewLock` votes. -/
  | certStatus (proper : ProperReport V) (certPairs : List (ViewLock V))
  /-- Subround 2: coordinator proposal for view `v`. -/
  | propose (view : ℕ) (prop : Proposal V)
  /-- Subround 3: Stage-1 echo/prevote for `(view, val)`. -/
  | echo (view : ℕ) (val : V)
  /-- Subround 4: Stage-2 vote for `(view, val)` (emitted after `n - t` echoes). -/
  | vote (view : ℕ) (val : V)
  /-- Subround 5: Stage-3 commit for `(view, val)` (emitted after `n - t` votes, upon locking). -/
  | commit (view : ℕ) (val : V)
  /-- Placeholder sent by non-leaders in Subround 2 or silent voters in Subrounds 3–5. -/
  | idle
  deriving @[expose] DecidableEq

/-- Local state of a process running `byzQuorumProtocol`. -/
structure ByzViewState (V : Type*) where
  /-- Process's initial input value. -/
  input : V
  /-- Highest `(view, val)` lock acquired after `n - t` Stage-2 votes (`none` initially). -/
  locked : Option (ViewLock V)
  /-- Write-once consensus decision (`none` until `n - t` Stage-3 commits are observed). -/
  decided : Option V
  /-- Append-only record of `(view, val)` Stage-2 votes emitted by this process. -/
  votedViews : List (ViewLock V)
  /-- Subround 0 → 1 properness summary. -/
  properReport : ProperReport V
  /-- Subround 0 → 1 `(t + 1)`-witnessed past vote pairs. -/
  certPairs : List (ViewLock V)
  /-- Subround 1 → 2 received properness reports for voter check. -/
  properSnapshot : List (ProperReport V)
  /-- Subround 1 → 2 `(t + 1)`-amplified view certificates accepted by a voter. -/
  voterCerts : List (ViewLock V)
  /-- Subround 1 → 2 proposal prepared if this process is the view coordinator. -/
  leaderProposal : Option (Proposal V)
  /-- Subround 2 → 3 Stage-1 echo value, if accepted. -/
  myEcho : Option V
  /-- Subround 3 → 4 Stage-2 vote value, if `n - t` echoes were observed. -/
  myVote : Option V
  /-- Subround 4 → 5 Stage-3 commit value, if `n - t` votes were observed. -/
  myCommit : Option V
  deriving @[expose] DecidableEq

/-- Initial local state of `byzQuorumProtocol` on input `v`. -/
@[expose] def byzInit {V : Type*} (v : V) : ByzViewState V where
  input := v
  locked := none
  decided := none
  votedViews := []
  properReport := ⟨false, []⟩
  certPairs := []
  properSnapshot := []
  voterCerts := []
  leaderProposal := none
  myEcho := none
  myVote := none
  myCommit := none

/-- Extracts the initial value from a Subround-0 `.rawStatus` message. -/
@[expose] def extractRawInit {V : Type*} : Option (ByzViewMsg V) → Option V
  | some (.rawStatus w _) => some w
  | _ => none

/-- Extracts the `votedViews` list from a Subround-0 `.rawStatus` message. -/
@[expose] def extractRawVotes {V : Type*} : Option (ByzViewMsg V) → List (ViewLock V)
  | some (.rawStatus _ vs) => vs
  | _ => []

/-- Number of distinct senders in `procs.dedup` reporting `lk` in Subround 0 for `lk.view < v`. -/
@[expose] def rawVoteCount {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (v : ℕ) (m : P → Option (ByzViewMsg V)) (lk : ViewLock V) : ℕ :=
  if lk.view < v then
    (procs.dedup.filter fun j => decide (lk ∈ extractRawVotes (m j))).length
  else 0

/-- Subround 0 properness computation from received `.rawStatus` messages. -/
@[expose] def computeProperReport {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (t : ℕ) (m : P → Option (ByzViewMsg V)) : ProperReport V :=
  let initFrom := fun j => extractRawInit (m j)
  let reported := procs.dedup.filter fun j => (initFrom j).isSome
  let allProp := decide (2 * t + 1 ≤ reported.length ∧
    ∀ j ∈ reported, t + 1 ≤ (reported.filter fun k => decide (initFrom k ≠ initFrom j)).length)
  let cands := (procs.dedup.filterMap initFrom).dedup
  let freq := cands.filter fun w => decide (t + 1 ≤ countVal procs initFrom w)
  ⟨allProp, freq⟩

/-- Subround 0 `(t + 1)`-witnessed `ViewLock` pairs for view `v`. -/
@[expose] def computeCertPairs {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (t v : ℕ) (m : P → Option (ByzViewMsg V)) : List (ViewLock V) :=
  let cands := (procs.dedup.flatMap fun j => extractRawVotes (m j)).dedup
  cands.filter fun lk => decide (t + 1 ≤ rawVoteCount procs v m lk)

/-- Extracts `(proper, certPairs)` from a Subround-1 `.certStatus` message. -/
@[expose] def extractCertStatus {V : Type*} :
    Option (ByzViewMsg V) → Option (ProperReport V × List (ViewLock V))
  | some (.certStatus rep cp) => some (rep, cp)
  | _ => none

/-- Count of distinct senders in `procs.dedup` whose `.certStatus` carries `lk` (`lk.view < v`). -/
@[expose] def certSupportCount {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (v : ℕ) (m : P → Option (ByzViewMsg V)) (lk : ViewLock V) : ℕ :=
  if lk.view < v then
    (procs.dedup.filter fun j =>
      match extractCertStatus (m j) with
      | some (_, cp) => decide (lk ∈ cp)
      | none => false).length
  else 0

/-- Number of `ProperReport` entries in `snaps` vouching for `w`. -/
@[expose] def properSupportCount {V : Type*} [DecidableEq V]
    (snaps : List (ProperReport V)) (w : V) : ℕ :=
  (snaps.filter fun rep => rep.allProper || decide (w ∈ rep.freqVals)).length

/-- Length of a filtered `filterMap` of `Prod.fst` over `(ProperReport, certPairs)` pairs. -/
theorem filterMap_fst_filter_length {P V : Type*}
    (l : List P) (f : P → Option (ProperReport V × List (ViewLock V)))
    (pred : ProperReport V → Bool) :
    ((l.filterMap fun j => (f j).map Prod.fst).filter pred).length =
      (l.filter fun j => match f j with | some (rep, _) => pred rep | none => false).length := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    rcases hfa : f a with _ | ⟨rep, _⟩
    · simp [hfa, ih]
    · cases hp : pred rep <;> simp [hfa, hp, ih]

/-- Whether `prop : Proposal V` is acceptable to a voter holding state `st`. -/
@[expose] def acceptsProposal {V : Type*} [DecidableEq V]
    (t : ℕ) (st : ByzViewState V) (prop : Proposal V) : Bool :=
  match prop.certView with
  | none =>
    st.locked.isNone && decide (t + 1 ≤ properSupportCount st.properSnapshot prop.val)
  | some u =>
    decide (⟨u, prop.val⟩ ∈ st.voterCerts) &&
      match st.locked with
      | none => true
      | some lk => decide (prop.val = lk.val ∨ lk.view ≤ u)

/-- Outgoing message of `byzQuorumProtocol` in round `r` (`v = r / 6`, subround `r % 6`). -/
@[expose] def byzSend {P V : Type*} [DecidableEq P]
    (leader : ℕ → P) (r : ℕ) (i : P) (st : ByzViewState V) : ByzViewMsg V :=
  let v := r / 6
  match r % 6 with
  | 0 => .rawStatus st.input st.votedViews
  | 1 => .certStatus st.properReport st.certPairs
  | 2 =>
    if i = leader v then
      match st.leaderProposal with
      | some prop => .propose v prop
      | none => .idle
    else .idle
  | 3 =>
    match st.myEcho with
    | some val => .echo v val
    | none => .idle
  | 4 =>
    match st.myVote with
    | some val => .vote v val
    | none => .idle
  | _ =>
    match st.myCommit with
    | some val => .commit v val
    | none => .idle

/-- Extracts a view-`v` `.echo` payload. -/
@[expose] def extractEcho {V : Type*} (v : ℕ) : Option (ByzViewMsg V) → Option V
  | some (.echo v' val) => if v' = v then some val else none
  | _ => none

/-- Extracts a view-`v` `.vote` payload. -/
@[expose] def extractVote {V : Type*} (v : ℕ) : Option (ByzViewMsg V) → Option V
  | some (.vote v' val) => if v' = v then some val else none
  | _ => none

/-- Extracts a view-`v` `.commit` payload. -/
@[expose] def extractCommit {V : Type*} (v : ℕ) : Option (ByzViewMsg V) → Option V
  | some (.commit v' val) => if v' = v then some val else none
  | _ => none

/-- Local state transition of `byzQuorumProtocol` at the end of round `r`. -/
@[expose] def byzUpdate {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (leader : ℕ → P) (t r : ℕ) (st : ByzViewState V)
    (m : P → Option (ByzViewMsg V)) : ByzViewState V :=
  let n := procs.dedup.length
  let q := n - t
  let v := r / 6
  match r % 6 with
  | 0 =>
    { st with
      properReport := computeProperReport procs t m
      certPairs := computeCertPairs procs t v m }
  | 1 =>
    let snaps := procs.dedup.filterMap fun j => (extractCertStatus (m j)).map Prod.fst
    let allCands := (procs.dedup.flatMap fun j =>
      ((extractCertStatus (m j)).map Prod.snd).getD []).dedup
    let vCerts := allCands.filter fun lk => decide (t + 1 ≤ certSupportCount procs v m lk)
    let lCerts := allCands.filter fun lk => decide (q ≤ certSupportCount procs v m lk)
    let lProp : Option (Proposal V) :=
      match pickMaxLock lCerts with
      | some best => some ⟨best.val, some best.view⟩
      | none =>
        let valCands := (st.input :: snaps.flatMap ProperReport.freqVals).dedup
        (valCands.find? fun w => decide (q ≤ properSupportCount snaps w)).map fun w => ⟨w, none⟩
    { st with
      properSnapshot := snaps
      voterCerts := vCerts
      leaderProposal := lProp }
  | 2 =>
    let echoVal : Option V :=
      match m (leader v) with
      | some (.propose v' prop) =>
        if v' = v ∧ acceptsProposal t st prop then some prop.val else none
      | _ => none
    { st with myEcho := echoVal }
  | 3 =>
    match findQuorumVal procs q (fun j => extractEcho v (m j)) with
    | some val =>
      let lk : ViewLock V := ⟨v, val⟩
      { st with
        myVote := some val
        votedViews := if lk ∈ st.votedViews then st.votedViews else lk :: st.votedViews }
    | none => { st with myVote := none }
  | 4 =>
    match findQuorumVal procs q (fun j => extractVote v (m j)) with
    | some val =>
      { st with
        locked := some ⟨v, val⟩
        myCommit := some val }
    | none => { st with myCommit := none }
  | _ =>
    match findQuorumVal procs q (fun j => extractCommit v (m j)) with
    | some val => { st with decided := st.decided.or (some val) }
    | none => st

/-- Original six-subround rotating-coordinator unauthenticated Byzantine quorum-locking
consensus protocol (`3 * t < Fintype.card P`) for the basic round model of
[Dwork, Lynch and Stockmeyer, §3.1][DworkLynchStockmeyer1988] (replacing Algorithm 3's alternating
trying/lock-release phases, monotone `PROPER`-set piggybacking, and continuous Srikanth–Toueg
broadcast in [§3.2.3][DworkLynchStockmeyer1988] with a two-round `t + 1` / `n - t` status and
input-properness relay plus echo, vote/lock, and commit quorums). `procs` enumerates `P`
(`∀ p : P, p ∈ procs`) so quorum thresholds and candidate selection are computable without
`[Fintype V]` or `Classical.choice`. -/
@[expose] def byzQuorumProtocol (P V : Type*) [DecidableEq P] [DecidableEq V]
    (procs : List P) (leader : ℕ → P) (t : ℕ) :
    PartialSyncProtocol P V (ByzViewState V) (ByzViewMsg V) where
  init _ v := byzInit v
  send r i st _ := byzSend leader r i st
  update r _ st m := byzUpdate procs leader t r st m
  output _ st := st.decided

/-! ### Unconditional pre-GST safety of `byzQuorumProtocol` -/

section ByzSafety

variable {P V : Type*} [DecidableEq P] [DecidableEq V]
variable {procs : List P} (leader : ℕ → P) {t : ℕ}

/-- Incoming message function for recipient `i` in round `r` of a `byzQuorumProtocol` run. -/
@[expose] def byzIncoming (procs : List P) (leader : ℕ → P) (t : ℕ)
    (F : Finset P) (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V))
    (x : P → V) (r : ℕ) (i : P) (j : P) : Option (ByzViewMsg V) :=
  if j ∈ F then adv r j i
  else if deliver r j i then
    some (byzSend leader r j
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r j))
  else none

/-- One-step unfolding equation for `byzQuorumProtocol`'s `byzantineState`. -/
theorem byzQuorum_state_succ (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) (r : ℕ) (i : P) :
    (byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i =
      byzUpdate procs leader t r
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i)
        (byzIncoming procs leader t F deliver adv x r i) := rfl

/-- `input` is invariant across all rounds of `byzQuorumProtocol`. -/
theorem byzState_input_eq (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) :
    ∀ r i, ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).input = x i
  | 0, _ => rfl
  | r + 1, i => by
    rw [byzQuorum_state_succ]; simp only [byzUpdate]
    split <;> (try split) <;> exact byzState_input_eq F deliver adv x r i

private theorem byzState_decided_unchanged_of_ne_five (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 5) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).decided =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).decided := by
  rw [byzQuorum_state_succ]
  rcases (by omega : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ r % 6 = 3 ∨ r % 6 = 4) with
    h | h | h | h | h <;> simp only [byzUpdate, h] <;> split <;> rfl

/-- Decisions of `byzQuorumProtocol` are write-once across all rounds. -/
theorem byzQuorum_irrevocable (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (i : P) (val : V)
    (hdec : (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r₁ i =
      some val) :
    (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r₂ i = some val := by
  induction hr with
  | refl => exact hdec
  | @step m _ ih =>
    by_cases hm5 : m % 6 = 5
    · rw [PartialSyncProtocol.byzantineDecision, byzQuorum_state_succ]
      simp only [byzUpdate, hm5]
      split
      · next w _ => exact congrArg (Option.or · (some w)) ih
      · exact ih
    · exact (byzState_decided_unchanged_of_ne_five leader F deliver adv x m hm5 i).trans ih

private theorem byzState_votedViews_unchanged_of_ne_three (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 3) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).votedViews =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).votedViews := by
  rw [byzQuorum_state_succ]; simp only [byzUpdate]
  split <;> (try split) <;> first | rfl | omega

/-- `votedViews` is monotone (append-only) across rounds of `byzQuorumProtocol`. -/
private theorem byzState_votedViews_mono (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (i : P) {lk : ViewLock V}
    (hlk : lk ∈
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r₁ i).votedViews) :
    lk ∈
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r₂ i).votedViews := by
  induction hr with
  | refl => exact hlk
  | @step m _ ih =>
    by_cases h3 : m % 6 = 3
    · rw [byzQuorum_state_succ]
      simp only [byzUpdate, h3]
      split <;> (try split_ifs) <;> simp [ih]
    · rwa [byzState_votedViews_unchanged_of_ne_three leader F deliver adv x m h3]

theorem byzState_locked_unchanged_of_ne_four (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 4) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).locked =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).locked := by
  rw [byzQuorum_state_succ]; simp only [byzUpdate]
  split <;> (try split) <;> first | rfl | omega

/-- `locked` is unchanged during Subrounds 0–3 of each view. -/
private theorem byzState_locked_eq_view_start (F : Finset P) (deliver : ℕ → P → P → Bool)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) {v k : ℕ} (hk : k ≤ 4) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (6 * v + k) i).locked =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (6 * v) i).locked := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (by omega)]
    exact byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + k) (by omega) i

/-- Every entry `lk ∈ st.votedViews` at round `r` was added in Subround 3 (`6 * lk.view + 3 < r`)
from a quorum of `n - t` `.echo lk.view lk.val` messages. -/
private theorem votedViews_origin [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) :
    ∀ r i {lk : ViewLock V},
      lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).votedViews →
      6 * lk.view + 3 < r ∧
        Fintype.card P - t ≤
          (Finset.univ.filter fun j =>
            extractEcho lk.view
              (byzIncoming procs leader t F deliver adv x (6 * lk.view + 3) i j) =
                some lk.val).card
  | 0, _, _, hlk => by
    simp only [PartialSyncProtocol.byzantineState, byzQuorumProtocol, byzInit,
      List.not_mem_nil] at hlk
  | r + 1, i, lk, hlk => by
    by_cases hr3 : r % 6 = 3
    · rw [byzQuorum_state_succ] at hlk
      simp only [byzUpdate, hr3] at hlk
      split at hlk
      · next val hfq =>
        split_ifs at hlk
        · exact (votedViews_origin hprocs hn r i hlk).imp_left Nat.lt_succ_of_lt
        · rcases List.mem_cons.1 hlk with rfl | hold
          · refine ⟨by dsimp only; omega, ?_⟩
            simpa only [show 6 * (r / 6) + 3 = r by omega] using
              findQuorumVal_dedup_sub hprocs (by omega) _ hfq
          · exact (votedViews_origin hprocs hn r i hold).imp_left Nat.lt_succ_of_lt
      · exact (votedViews_origin hprocs hn r i hlk).imp_left Nat.lt_succ_of_lt
    · rw [byzState_votedViews_unchanged_of_ne_three leader F deliver adv x r hr3 i] at hlk
      exact (votedViews_origin hprocs hn r i hlk).imp_left Nat.lt_succ_of_lt

private theorem byzIncoming_honest_deliver {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    {r : ℕ} {i h : P} (hhF : h ∉ F) {g : Option (ByzViewMsg V) → Option V}
    (hnone : g none = none) {w : V}
    (hg : g (byzIncoming procs leader t F deliver adv x r i h) = some w) :
    g (some (byzSend leader r h
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r h))) = some w := by
  simp only [byzIncoming, hhF, ↓reduceIte] at hg
  split_ifs at hg
  · exact hg
  · simp only [hnone, reduceCtorEq] at hg

/-- A view-`v` echo received from a correct sender `h` is `h`'s `myEcho`. -/
private theorem honest_echo_eq {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V} {v : ℕ} {i h : P} {w : V}
    (hhF : h ∉ F)
    (hw : extractEcho v (byzIncoming procs leader t F deliver adv x (6 * v + 3) i h) = some w) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (6 * v + 3) h).myEcho =
      some w := by
  have hw := byzIncoming_honest_deliver leader hhF rfl hw
  simp only [byzSend, show (6 * v + 3) % 6 = 3 by omega, show (6 * v + 3) / 6 = v by omega] at hw
  split at hw <;> simp_all [extractEcho]

/-- At most one value can ever appear in `votedViews` at a given view `u` across all processes
(even across distinct processes and arbitrary rounds). -/
private theorem votedViews_unique_in_view [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {r₁ r₂ : ℕ} {i₁ i₂ : P} {u : ℕ} {v₁ v₂ : V}
    (h₁ : ⟨u, v₁⟩ ∈
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r₁ i₁).votedViews)
    (h₂ : ⟨u, v₂⟩ ∈
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r₂ i₂).votedViews) :
    v₁ = v₂ :=
  prevoteQuorum_unique hn hF (fun _ hhF _ hw => honest_echo_eq leader hhF hw)
    (fun _ hhF _ hw => honest_echo_eq leader hhF hw)
    (votedViews_origin leader hprocs hn r₁ i₁ h₁).2 (votedViews_origin leader hprocs hn r₂ i₂ h₂).2

omit [DecidableEq P] in
/-- A duplicate-free list of more than `t ≥ F.card` processes contains a correct one. -/
private theorem exists_mem_notMem_of_lt_length {F : Finset P} (hF : F.card ≤ t) {l : List P}
    (hl : l.Nodup) (h : t < l.length) : ∃ j ∈ l, j ∉ F := by
  classical
  rw [← List.toFinset_card_of_nodup hl] at h
  obtain ⟨j, hj, hjF⟩ := Finset.exists_mem_notMem_of_card_lt_card (hF.trans_lt h)
  exact ⟨j, List.mem_toFinset.1 hj, hjF⟩

/-- Soundness of Subround-0 `certPairs`: if `lk ∈ certPairs` after Subround 0 of view `v`,
then `lk.view < v` and some correct process `h ∉ F` already held `lk ∈ votedViews` at `6 * v`. -/
private theorem certPairs_sound {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hF : F.card ≤ t) (v : ℕ) (i : P) {lk : ViewLock V}
    (hlk : lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v + 1) i).certPairs) :
    lk.view < v ∧ ∃ h ∉ F, lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v) h).votedViews := by
  have hd0 : 6 * v / 6 = v := by omega
  rw [byzQuorum_state_succ] at hlk
  simp only [byzUpdate, Nat.mul_mod_right, hd0, computeCertPairs, List.mem_filter,
    decide_eq_true_eq, rawVoteCount] at hlk
  obtain ⟨-, hcnt⟩ := hlk
  split_ifs at hcnt with hlt
  · obtain ⟨h, hh, hhF⟩ :=
      exists_mem_notMem_of_lt_length hF ((List.nodup_dedup procs).filter _) hcnt
    simp only [List.mem_filter, byzIncoming, hhF, ↓reduceIte, decide_eq_true_eq] at hh
    split_ifs at hh <;>
      simp only [byzSend, Nat.mul_mod_right, extractRawVotes, List.not_mem_nil, and_false] at hh
    exact ⟨hlt, h, hhF, hh.2⟩
  · omega

/-- **Unforgeability of unauthenticated view certificates (`voterCerts_sound`):** if `lk` is in
`voterCerts` at the end of Subround 1 of view `v` (`6 * v + 2`), then `lk.view < v` and some
correct process `h ∉ F` held `lk ∈ votedViews` at round `6 * v`. -/
theorem voterCerts_sound {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hF : F.card ≤ t) (v : ℕ) (i : P) {lk : ViewLock V}
    (hlk : lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v + 2) i).voterCerts) :
    lk.view < v ∧ ∃ h ∉ F, lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v) h).votedViews := by
  have hm1 : (6 * v + 1) % 6 = 1 := by omega
  rw [show 6 * v + 2 = (6 * v + 1) + 1 by omega, byzQuorum_state_succ] at hlk
  simp only [byzUpdate, hm1, show (6 * v + 1) / 6 = v by omega, List.mem_filter,
    decide_eq_true_eq, certSupportCount] at hlk
  obtain ⟨-, hcnt⟩ := hlk
  split_ifs at hcnt with hlt
  · obtain ⟨r, hr, hrF⟩ :=
      exists_mem_notMem_of_lt_length hF ((List.nodup_dedup procs).filter _) hcnt
    simp only [List.mem_filter, byzIncoming, hrF, ↓reduceIte] at hr
    split_ifs at hr <;> simp only [byzSend, hm1, extractCertStatus, decide_eq_true_eq,
      Bool.false_eq_true, and_false] at hr
    exact certPairs_sound leader hF v r hr.2
  · omega

/-- Every lock `locked = some lk` held at round `r` satisfies `6 * lk.view + 4 < r` and is backed
by at least `n - 2 * t` correct processes `h ∉ F` holding `lk ∈ votedViews` at round `r`. -/
theorem byzState_locked_witness [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) :
    ∀ r i {lk : ViewLock V},
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).locked =
        some lk →
      6 * lk.view + 4 < r ∧
        Fintype.card P - 2 * t ≤
          ((Finset.univ \ F).filter fun h =>
            lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
              F deliver adv x r h).votedViews).card
  | 0, _, _, hlk => by
    simp only [PartialSyncProtocol.byzantineState, byzQuorumProtocol, byzInit, reduceCtorEq] at hlk
  | r + 1, i, lk, hlk => by
    -- Correct witnesses persist from round `r` to `r + 1`.
    have hmono (lk : ViewLock V) := Finset.card_le_card
      (Finset.monotone_filter_right (Finset.univ \ F) fun h _ hm =>
        byzState_votedViews_mono (procs := procs) leader (t := t) F deliver adv x
          (Nat.le_add_right r 1) h (lk := lk) hm)
    by_cases hkeep :
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).locked = some lk
    · obtain ⟨hlt, hcard⟩ := byzState_locked_witness hprocs hn hF r i hkeep
      exact ⟨by omega, hcard.trans (hmono lk)⟩
    have hr4 : r % 6 = 4 := by_contra fun hr4 =>
      hkeep (by rwa [byzState_locked_unchanged_of_ne_four leader F deliver adv x r hr4 i] at hlk)
    rw [byzQuorum_state_succ] at hlk
    simp only [byzUpdate, hr4] at hlk
    split at hlk
    · next val hfq =>
      cases hlk
      -- Each correct sender of a view-`r / 6` vote for `val` recorded `⟨r / 6, val⟩` in Subround 3.
      have hsub : (Finset.univ.filter fun j =>
          extractVote (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some val) \ F ⊆
          (Finset.univ \ F).filter fun h => (⟨r / 6, val⟩ : ViewLock V) ∈
            ((byzQuorumProtocol P V procs leader t).byzantineState
              F deliver adv x r h).votedViews := by
        intro h hh
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
        refine ⟨hh.2, ?_⟩
        have hv := byzIncoming_honest_deliver leader hh.2 rfl hh.1
        simp only [byzSend, hr4] at hv
        split at hv
        · next w hmv =>
          simp only [extractVote, ↓reduceIte, Option.some.injEq] at hv
          subst hv
          obtain ⟨v, rfl⟩ : ∃ v, r = 6 * v + 3 + 1 := ⟨r / 6, by omega⟩
          rw [byzQuorum_state_succ] at hmv ⊢
          simp only [byzUpdate, show (6 * v + 3) % 6 = 3 by omega,
            show (6 * v + 3) / 6 = v by omega, show (6 * v + 3 + 1) / 6 = v by omega] at hmv ⊢
          split at hmv
          · cases hmv
            split_ifs with hm
            exacts [hm, List.mem_cons_self]
          · cases hmv
        · simp [extractVote] at hv
      have := findQuorumVal_dedup_sub hprocs (by omega) _ hfq
      have := Finset.le_card_sdiff F (Finset.univ.filter fun j =>
        extractVote (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some val)
      have := (Finset.card_le_card hsub).trans (hmono _)
      exact ⟨by dsimp only; omega, by omega⟩
    · exact absurd hlk hkeep

/-- A lock held by any process is backed by a correct process's Stage-2 vote. -/
private theorem byzState_locked_voter [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r : ℕ} {i : P}
    {lk : ViewLock V}
    (hlk : ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).locked =
      some lk) :
    ∃ h ∉ F, lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x r h).votedViews := by
  obtain ⟨_, hwit⟩ := byzState_locked_witness leader hprocs hn hF r i hlk
  obtain ⟨h, hh⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit)
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh
  exact ⟨h, hh⟩

/-- Every first decision `some val₀` at step `r → r + 1` occurs in Subround 5 (`r % 6 = 5`) of view
`v₀ = r / 6` and yields a set of at least `n - 2 * t` correct processes holding
`locked = some ⟨v₀, val₀⟩` at round `r + 1`. -/
private theorem decision_step_locks [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {r : ℕ} {i : P} {val₀ : V}
    (hnone : ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x r i).decided = none)
    (hsome : ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (r + 1) i).decided = some val₀) :
    r % 6 = 5 ∧
      Fintype.card P - 2 * t ≤
        ((Finset.univ \ F).filter fun q =>
          ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x (r + 1) q).locked = some ⟨r / 6, val₀⟩).card := by
  have hr5 : r % 6 = 5 := by_contra fun hne => by
    simp [byzState_decided_unchanged_of_ne_five leader F deliver adv x r hne i, hnone] at hsome
  refine ⟨hr5, ?_⟩
  rw [byzQuorum_state_succ] at hsome
  simp only [byzUpdate, hr5] at hsome
  split at hsome
  · next w hfq =>
    simp only [hnone, Option.none_or, Option.some.injEq] at hsome
    subst hsome
    -- Every correct sender of a view-`r / 6` commit for `w` locked `⟨r / 6, w⟩` in Subround 4.
    have hsub : (Finset.univ.filter fun j =>
        extractCommit (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some w) \ F ⊆
        (Finset.univ \ F).filter fun q =>
          ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x (r + 1) q).locked = some ⟨r / 6, w⟩ := by
      intro q hq
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨hq.2, ?_⟩
      rw [byzState_locked_unchanged_of_ne_four leader F deliver adv x r (by omega) q]
      have hc := byzIncoming_honest_deliver leader hq.2 rfl hq.1
      simp only [byzSend, hr5] at hc
      split at hc
      · next u hmc =>
        simp only [extractCommit, ↓reduceIte, Option.some.injEq] at hc
        subst hc
        obtain ⟨v, rfl⟩ : ∃ v, r = 6 * v + 4 + 1 := ⟨r / 6, by omega⟩
        rw [byzQuorum_state_succ] at hmc ⊢
        simp only [byzUpdate, show (6 * v + 4) % 6 = 4 by omega,
          show (6 * v + 4) / 6 = v by omega, show (6 * v + 4 + 1) / 6 = v by omega] at hmc ⊢
        split at hmc
        · cases hmc; rfl
        · cases hmc
      · simp [extractCommit] at hc
    have := findQuorumVal_dedup_sub hprocs (by omega) _ hfq
    have := Finset.le_card_sdiff F (Finset.univ.filter fun j =>
      extractCommit (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some w)
    have := Finset.card_le_card hsub
    omega
  · simp only [hnone, reduceCtorEq] at hsome

/-- Any `.echo v val` received from a correct sender `h ∉ F` in Subround 3 (`6 * v + 3`) came from a
proposal `prop` with `prop.val = val` accepted by `h` at round `6 * v + 2`. -/
private theorem honest_echo_accepted {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    {v : ℕ} {p h : P} {val : V} (hhF : h ∉ F)
    (hecho : extractEcho v (byzIncoming procs leader t F deliver adv x (6 * v + 3) p h) =
      some val) :
    ∃ prop : Proposal V, prop.val = val ∧
      acceptsProposal t ((byzQuorumProtocol P V procs leader t).byzantineState
        F deliver adv x (6 * v + 2) h) prop = true := by
  have hme := honest_echo_eq leader hhF hecho
  rw [show 6 * v + 3 = (6 * v + 2) + 1 from rfl, byzQuorum_state_succ] at hme
  simp only [byzUpdate, show (6 * v + 2) % 6 = 2 by omega,
    show (6 * v + 2) / 6 = v by omega] at hme
  split at hme
  · split_ifs at hme with hacc
    cases hme
    exact ⟨_, rfl, hacc.2⟩
  · simp only [reduceCtorEq] at hme

/-- **Cross-view lock preservation (`byzQuorum_lock_preservation`):** suppose
`3 * t < Fintype.card P`, `F.card ≤ t`, and a set `L₀ ⊆ Finset.univ \ F` of at least `n - 2 * t`
correct processes holds `locked = some ⟨v₀, val₀⟩` at the end of view `v₀` (`6 * (v₀ + 1)`). Then
across all views `v ≥ v₀` and all rounds `r`:
1. Every Stage-2 vote `⟨v, val⟩ ∈ votedViews` with `v₀ ≤ v` has `val = val₀`.
2. At the end of every view `v ≥ v₀` (`6 * (v + 1)`), every `q ∈ L₀` holds `locked = some lk` with
   `v₀ ≤ lk.view` and `lk.val = val₀`. -/
theorem byzQuorum_lock_preservation [Fintype P] {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {v₀ : ℕ} {val₀ : V} {L₀ : Finset P}
    (hL₀_sub : L₀ ⊆ Finset.univ \ F) (hL₀_card : Fintype.card P - 2 * t ≤ L₀.card)
    (hL₀_lock : ∀ q ∈ L₀, ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * (v₀ + 1)) q).locked = some ⟨v₀, val₀⟩) :
    ∀ d : ℕ,
      (∀ r p val, ⟨v₀ + d, val⟩ ∈
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r p).votedViews →
        val = val₀) ∧
      (∀ q ∈ L₀, ∃ u_q, v₀ ≤ u_q ∧
        ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (6 * (v₀ + d + 1)) q).locked = some ⟨u_q, val₀⟩) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    have hv_vote : ∀ r p val, ⟨v₀ + d, val⟩ ∈
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r p).votedViews →
        val = val₀ := by
      intro r p val hmem
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · obtain ⟨q₀, hq₀⟩ := Finset.card_pos.1 (by omega : 0 < L₀.card)
        obtain ⟨h₀, -, hh₀⟩ := byzState_locked_voter leader hprocs hn hF (hL₀_lock q₀ hq₀)
        exact votedViews_unique_in_view leader hprocs hn hF hmem hh₀
      by_contra hne_val
      obtain ⟨_, hq_echo⟩ := votedViews_origin leader hprocs hn r p hmem
      dsimp only at hq_echo
      set v := v₀ + d
      -- Some correct process `qStar ∈ L₀` echoed `val`, so it accepted a proposal for `val`.
      obtain ⟨qStar, hqInter, -⟩ := quorum_inter_notMem (F := ∅)
        (S₁ := Finset.univ.filter fun j =>
          extractEcho v (byzIncoming procs leader t F deliver adv x (6 * v + 3) p j) = some val)
        (S₂ := L₀)
        (by simp only [Finset.card_empty]; omega)
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hqInter
      rcases hqInter with ⟨hqE, hqL₀⟩
      have hqF : qStar ∉ F := (Finset.mem_sdiff.1 (hL₀_sub hqL₀)).2
      obtain ⟨u_q, hu_ge, hqlk0⟩ := (ih (d - 1) (by omega)).2 qStar hqL₀
      rw [show v₀ + (d - 1) + 1 = v by omega] at hqlk0
      have hqlk2 := (byzState_locked_eq_view_start leader F deliver adv x (k := 2) (by omega)
        qStar).trans hqlk0
      obtain ⟨prop, rfl, hacc⟩ := honest_echo_accepted leader hqF hqE
      simp only [acceptsProposal, hqlk2] at hacc
      cases hcv : prop.certView with
      | none => simp only [hcv, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at hacc
      | some u_cert =>
        simp only [hcv, Bool.and_eq_true, decide_eq_true_eq] at hacc
        have hu_le : u_q ≤ u_cert := hacc.2.resolve_left hne_val
        -- The certificate is backed by a correct vote from an earlier view `u_cert ≥ v₀`.
        obtain ⟨hu_lt, h', -, hh'mem⟩ := voterCerts_sound leader hF v qStar hacc.1
        have hu_lt' : u_cert < v₀ + d := hu_lt
        refine hne_val ((ih (u_cert - v₀) (by omega)).1 (6 * v) h' prop.val ?_)
        rwa [show v₀ + (u_cert - v₀) = u_cert by omega]
    refine ⟨hv_vote, fun q hq => ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · exact ⟨v₀, le_rfl, hL₀_lock q hq⟩
    set v := v₀ + d
    obtain ⟨u_prev, hu_prev, hlk_prev⟩ := (ih (d - 1) (by omega)).2 q hq
    rw [show v₀ + (d - 1) + 1 = v by omega] at hlk_prev
    have hlk4 := (byzState_locked_eq_view_start leader F deliver adv x (k := 4) (by omega)
      q).trans hlk_prev
    have hm4 : (6 * v + 4) % 6 = 4 := by omega
    have hd4 : (6 * v + 4) / 6 = v := by omega
    rw [show 6 * (v + 1) = 6 * v + 4 + 1 + 1 by omega,
      byzState_locked_unchanged_of_ne_four leader F deliver adv x _ (by omega)]
    cases hfq4 : findQuorumVal procs (procs.dedup.length - t)
        (fun j => extractVote v (byzIncoming procs leader t F deliver adv x (6 * v + 4) q j)) with
    | none =>
      rw [byzQuorum_state_succ]
      simp only [byzUpdate, hm4, hd4, hfq4]
      exact ⟨u_prev, hu_prev, hlk4⟩
    | some w =>
      -- A fresh view-`v` lock is backed by correct Stage-2 votes, which must carry `val₀`.
      have hw_lk : ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (6 * v + 4 + 1) q).locked = some ⟨v, w⟩ := by
        rw [byzQuorum_state_succ]
        simp only [byzUpdate, hm4, hd4, hfq4]
      obtain ⟨h, -, hh⟩ := byzState_locked_voter leader hprocs hn hF hw_lk
      exact ⟨v, by omega, by rw [hw_lk, hv_vote _ h w hh]⟩

private theorem first_decision_round {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V} :
    ∀ r i {val : V},
      (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r i = some val →
      ∃ m < r,
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x m i).decided =
          none ∧
        ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (m + 1) i).decided = some val
  | 0, _, _, h => by
    simp only [PartialSyncProtocol.byzantineDecision, PartialSyncProtocol.byzantineState,
      byzQuorumProtocol, byzInit, reduceCtorEq] at h
  | r + 1, i, val, h => by
    cases hprev : ((byzQuorumProtocol P V procs leader t).byzantineState
        F deliver adv x r i).decided with
    | none => exact ⟨r, Nat.lt_succ_self r, hprev, h⟩
    | some w =>
      obtain rfl := Option.some.inj
        ((byzQuorum_irrevocable leader F deliver adv x r.le_succ i w hprev).symm.trans h)
      exact (first_decision_round r i hprev).imp fun _ hm => ⟨Nat.lt_succ_of_lt hm.1, hm.2⟩

/-- **Unconditional pre-GST global agreement (`byzQuorum_agreement`):** for `3 * t < Fintype.card P`
and `F.card ≤ t`, no two processes ever decide distinct values in `byzQuorumProtocol` (even under
arbitrary pre-GST message loss and without `GST` ever holding). -/
theorem byzQuorum_agreement [Fintype P] {F : Finset P} (hprocs : ∀ p : P, p ∈ procs)
    (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    {r₁ r₂ : ℕ} {i j : P} {v₁ v₂ : V}
    (h₁ : (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r₁ i = some v₁)
    (h₂ : (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r₂ j = some v₂) :
    v₁ = v₂ := by
  obtain ⟨m₁, -, hm₁n, hm₁s⟩ := first_decision_round leader r₁ i h₁
  obtain ⟨m₂, -, hm₂n, hm₂s⟩ := first_decision_round leader r₂ j h₂
  obtain ⟨hr₁5, hL₁⟩ := decision_step_locks leader hprocs hn hF hm₁n hm₁s
  obtain ⟨hr₂5, hL₂⟩ := decision_step_locks leader hprocs hn hF hm₂n hm₂s
  rw [show m₁ + 1 = 6 * (m₁ / 6 + 1) by omega] at hL₁
  rw [show m₂ + 1 = 6 * (m₂ / 6 + 1) by omega] at hL₂
  obtain ⟨q₁, hq₁⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL₁)
  obtain ⟨q₂, hq₂⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL₂)
  obtain ⟨h₁', -, hh₁'⟩ := byzState_locked_voter leader hprocs hn hF (Finset.mem_filter.1 hq₁).2
  obtain ⟨h₂', -, hh₂'⟩ := byzState_locked_voter leader hprocs hn hF (Finset.mem_filter.1 hq₂).2
  rcases le_total (m₁ / 6) (m₂ / 6) with hle | hle
  · exact ((byzQuorum_lock_preservation leader hprocs hn hF (Finset.filter_subset _ _) hL₁
      (fun q hq => (Finset.mem_filter.1 hq).2) (m₂ / 6 - m₁ / 6)).1 (6 * (m₂ / 6 + 1)) h₂' v₂
      (by rwa [Nat.add_sub_of_le hle])).symm
  · exact (byzQuorum_lock_preservation leader hprocs hn hF (Finset.filter_subset _ _) hL₂
      (fun q hq => (Finset.mem_filter.1 hq).2) (m₁ / 6 - m₂ / 6)).1 (6 * (m₁ / 6 + 1)) h₁' v₁
      (by rwa [Nat.add_sub_of_le hle])

/-- When all correct processes start with `val₀` (`∀ h ∉ F, x h = val₀`) and `F.card ≤ t`, every
process's Subround-0 `properReport` has `allProper = false` and `freqVals ⊆ {val₀}`. -/
private theorem properReport_unanimous {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V} {val₀ : V}
    (hF : F.card ≤ t) (hx : ∀ h ∉ F, x h = val₀) (v : ℕ) (i : P) :
    let rep := ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v + 1) i).properReport
    rep.allProper = false ∧ ∀ w ∈ rep.freqVals, w = val₀ := by
  have hd0 : 6 * v / 6 = v := by omega
  rw [byzQuorum_state_succ]
  simp only [byzUpdate, Nat.mul_mod_right, hd0, computeProperReport]
  let initFrom := fun j =>
    extractRawInit (byzIncoming procs leader t F deliver adv x (6 * v) i j)
  have hhonest_val : ∀ h ∉ F, ∀ w, initFrom h = some w → w = val₀ := fun h hhF w hw => by
    have hw' := byzIncoming_honest_deliver (g := extractRawInit) leader hhF rfl hw
    simpa [byzSend, Nat.mul_mod_right, extractRawInit, byzState_input_eq, hx h hhF] using hw'.symm
  constructor
  · rw [decide_eq_false_iff_not]
    rintro ⟨hrep_len, hall⟩
    change 2 * t + 1 ≤ (procs.dedup.filter fun j => (initFrom j).isSome).length at hrep_len
    have hnd_rep := (List.nodup_dedup procs).filter fun j => (initFrom j).isSome
    obtain ⟨h₀, hh₀, hh₀F⟩ := exists_mem_notMem_of_lt_length hF hnd_rep (by omega)
    obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 (List.mem_filter.1 hh₀).2
    -- More than `t` reporters disagree with the correct `h₀`, so one of them is correct.
    obtain ⟨k, hk, hkF⟩ := exists_mem_notMem_of_lt_length hF (hnd_rep.filter _) (hall h₀ hh₀)
    simp only [List.mem_filter, decide_eq_true_eq] at hk
    obtain ⟨wk, hwk⟩ := Option.isSome_iff_exists.1 hk.1.2
    exact hk.2 (show initFrom k = initFrom h₀ by
      rw [hwk, hw₀, hhonest_val k hkF wk hwk, hhonest_val h₀ hh₀F w₀ hw₀])
  · intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨h, hh, hhF⟩ :=
      exists_mem_notMem_of_lt_length hF ((List.nodup_dedup procs).filter _) hw.2
    simp only [List.mem_filter, decide_eq_true_eq] at hh
    exact hhonest_val h hhF w hh.2

/-- **Unconditional strong validity (`byzQuorum_validity`):** when `3 * t < Fintype.card P`,
`F.card ≤ t`, and every correct process starts with `val₀` (`∀ h ∉ F, x h = val₀`), no process ever
decides any value `w ≠ val₀` in `byzQuorumProtocol` (even without `GST`). -/
theorem byzQuorum_validity [Fintype P] {F : Finset P} (hprocs : ∀ p : P, p ∈ procs)
    (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V))
    {x : P → V} {val₀ : V} (hx : ∀ h ∉ F, x h = val₀) :
    ∀ r i {w : V},
      (byzQuorumProtocol P V procs leader t).byzantineDecision F deliver adv x r i = some w →
      w = val₀ := by
  have hvote_valid : ∀ u r p w,
      ⟨u, w⟩ ∈
        ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r p).votedViews →
      w = val₀ := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro r p w hmem
      obtain ⟨_, hq⟩ := votedViews_origin leader hprocs hn r p hmem
      dsimp only at hq
      obtain ⟨h, hh, hhF⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show F.card < (Finset.univ.filter fun j =>
          extractEcho u (byzIncoming procs leader t F deliver adv x (6 * u + 3) p j) =
            some w).card by omega)
      rw [Finset.mem_filter] at hh
      obtain ⟨prop, hprop_val, hacc⟩ := honest_echo_accepted leader hhF hh.2
      subst hprop_val
      simp only [acceptsProposal] at hacc
      cases hcv : prop.certView with
      | none =>
        simp only [hcv, Bool.and_eq_true, decide_eq_true_eq] at hacc
        have hcnt := hacc.2
        have hm1 : (6 * u + 1) % 6 = 1 := by omega
        rw [show 6 * u + 2 = (6 * u + 1) + 1 by omega, byzQuorum_state_succ] at hcnt
        simp only [byzUpdate, hm1, properSupportCount, filterMap_fst_filter_length] at hcnt
        -- A correct process vouched for `prop.val` in its Subround-0 properness report.
        obtain ⟨r', hr', hr'F⟩ :=
          exists_mem_notMem_of_lt_length hF ((List.nodup_dedup procs).filter _) hcnt
        simp only [List.mem_filter, byzIncoming, hr'F, ↓reduceIte] at hr'
        split_ifs at hr' <;> simp only [byzSend, hm1, extractCertStatus, Bool.or_eq_true,
          decide_eq_true_eq, Bool.false_eq_true, and_false] at hr'
        obtain ⟨hap, hfv⟩ := properReport_unanimous leader hF hx u r'
        exact hfv prop.val (hr'.2.resolve_left (by simp [hap]))
      | some u_cert =>
        simp only [hcv, Bool.and_eq_true, decide_eq_true_eq] at hacc
        obtain ⟨hu_lt, h', -, hh'mem⟩ := voterCerts_sound leader hF u h hacc.1
        exact ih u_cert hu_lt (6 * u) h' prop.val hh'mem
  intro r i w hdec
  obtain ⟨m, -, hmn, hms⟩ := first_decision_round leader r i hdec
  obtain ⟨_, hL⟩ := decision_step_locks leader hprocs hn hF hmn hms
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL)
  obtain ⟨h, -, hh⟩ := byzState_locked_voter leader hprocs hn hF (Finset.mem_filter.1 hq).2
  exact hvote_valid (m / 6) (m + 1) h w hh

end ByzSafety

/-! ### Crash/omission 3-subround view-locking protocol (`2 * t < Fintype.card P`) -/

/-- Messages exchanged by `omissionQuorumProtocol` across the 3 subrounds of each view `v`. -/
inductive OmissionViewMsg (V : Type*) where
  /-- Subround 0: sender's initial value and current highest `ViewLock`, if any. -/
  | status (initVal : V) (locked : Option (ViewLock V))
  /-- Subround 1: coordinator proposal for view `v`. -/
  | propose (view : ℕ) (prop : Proposal V)
  /-- Subround 2: acknowledgment that the sender locked `(view, val)`. -/
  | ack (view : ℕ) (val : V)
  /-- Placeholder sent by non-coordinators in Subround 1 or silent voters in Subround 2. -/
  | idle
  deriving @[expose] DecidableEq

/-- Local state of a process running `omissionQuorumProtocol`. -/
structure OmissionViewState (V : Type*) where
  /-- Process's initial input value. -/
  input : V
  /-- Highest `(view, val)` lock acquired upon accepting a proposal (`none` initially). -/
  locked : Option (ViewLock V)
  /-- Write-once consensus decision (`none` until `n - t` acknowledgments are observed). -/
  decided : Option V
  /-- Subround 0 → 1 proposal prepared if this process is the view coordinator. -/
  leaderProposal : Option (Proposal V)
  /-- Subround 1 → 2 acknowledgment value, if a proposal was accepted in Subround 1. -/
  myAck : Option V
  deriving @[expose] DecidableEq

/-- Outgoing message of `omissionQuorumProtocol` in round `r` (`v = r / 3`, subround `r % 3`). -/
@[expose] def omissionSend {P V : Type*} [DecidableEq P]
    (leader : ℕ → P) (r : ℕ) (i : P) (st : OmissionViewState V) : OmissionViewMsg V :=
  let v := r / 3
  match r % 3 with
  | 0 => .status st.input st.locked
  | 1 =>
    if i = leader v then
      match st.leaderProposal with
      | some prop => .propose v prop
      | none => .idle
    else .idle
  | _ =>
    match st.myAck with
    | some val => .ack v val
    | none => .idle

/-- Whether an omission-protocol voter in state `st` accepts `prop` in view `v` (`v' = v`). -/
@[expose] def acceptsOmissionProposal {V : Type*} [DecidableEq V]
    (v v' : ℕ) (st : OmissionViewState V) (prop : Proposal V) : Bool :=
  decide (v' = v) &&
  match st.locked, prop.certView with
  | none, _ => true
  | some lk, none => decide (prop.val = lk.val)
  | some lk, some u => decide (prop.val = lk.val ∨ lk.view ≤ u)

/-- Extracts a view-`v` `.ack` payload. -/
@[expose] def extractAck {V : Type*} (v : ℕ) : Option (OmissionViewMsg V) → Option V
  | some (.ack v' val) => if v' = v then some val else none
  | _ => none

/-- Whether a received `OmissionViewMsg` is a Subround-0 `.status` message. -/
@[expose] def isOmissionStatus {V : Type*} : Option (OmissionViewMsg V) → Bool
  | some (.status _ _) => true
  | _ => false

/-- Extracts the optional `ViewLock` from a Subround-0 `.status` message. -/
@[expose] def extractStatusLock {V : Type*} : Option (OmissionViewMsg V) → Option (ViewLock V)
  | some (.status _ (some lk)) => some lk
  | _ => none

/-- Local state transition of `omissionQuorumProtocol` at the end of round `r`. -/
@[expose] def omissionUpdate {P V : Type*} [DecidableEq P] [DecidableEq V]
    (procs : List P) (leader : ℕ → P) (t r : ℕ) (st : OmissionViewState V)
    (m : P → Option (OmissionViewMsg V)) : OmissionViewState V :=
  let q := procs.dedup.length - t
  let v := r / 3
  match r % 3 with
  | 0 =>
    let cnt := (procs.dedup.filter fun j => isOmissionStatus (m j)).length
    let lProp : Option (Proposal V) :=
      if q ≤ cnt then
        let locks := procs.dedup.filterMap fun j => extractStatusLock (m j)
        match pickMaxLock locks with
        | some best => some ⟨best.val, some best.view⟩
        | none => some ⟨st.input, none⟩
      else none
    { st with leaderProposal := lProp }
  | 1 =>
    match m (leader v) with
    | some (.propose v' prop) =>
      if acceptsOmissionProposal v v' st prop then
        { st with locked := some ⟨v, prop.val⟩, myAck := some prop.val }
      else { st with myAck := none }
    | _ => { st with myAck := none }
  | _ =>
    match findQuorumVal procs q (fun j => extractAck v (m j)) with
    | some val => { st with decided := st.decided.or (some val) }
    | none => st

/-- Original three-subround rotating-coordinator crash/omission quorum-locking consensus
protocol (`2 * t < Fintype.card P`) for the basic round model of
[Dwork, Lynch and Stockmeyer, §3.1][DworkLynchStockmeyer1988] (replacing Algorithm 1's alternating
trying/lock-release phases and monotone `PROPER`-set piggybacking in
[§3.2.1][DworkLynchStockmeyer1988] with single-lock status reporting, proposal/locking, and
`n - t` acknowledgments). -/
@[expose] def omissionQuorumProtocol (P V : Type*) [DecidableEq P] [DecidableEq V]
    (procs : List P) (leader : ℕ → P) (t : ℕ) :
    PartialSyncProtocol P V (OmissionViewState V) (OmissionViewMsg V) where
  init _ v := ⟨v, none, none, none, none⟩
  send r i st _ := omissionSend leader r i st
  update r _ st m := omissionUpdate procs leader t r st m
  output _ st := st.decided

/-! ### Unconditional pre-GST safety of `omissionQuorumProtocol` -/

section OmissionSafety

variable {P V : Type*} [DecidableEq P] [DecidableEq V]
variable {procs : List P} (leader : ℕ → P) {t : ℕ}

/-- Incoming message function for recipient `i` in round `r` of an `omissionQuorumProtocol` run. -/
@[expose] def omissionIncoming (procs : List P) (leader : ℕ → P) (t : ℕ)
    (deliver : ℕ → P → P → Bool) (x : P → V) (r : ℕ) (i : P) (j : P) :
    Option (OmissionViewMsg V) :=
  if deliver r j i then
    some (omissionSend leader r j
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r j))
  else none

/-- One-step unfolding equation for `omissionQuorumProtocol`'s `omissionState`. -/
theorem omissionQuorum_state_succ (deliver : ℕ → P → P → Bool) (x : P → V) (r : ℕ) (i : P) :
    (omissionQuorumProtocol P V procs leader t).omissionState deliver x (r + 1) i =
      omissionUpdate procs leader t r
        ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i)
        (omissionIncoming procs leader t deliver x r i) := rfl

/-- `input` is invariant across all rounds of `omissionQuorumProtocol`. -/
private theorem omissionState_input_eq (deliver : ℕ → P → P → Bool) (x : P → V) :
    ∀ r i, ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).input = x i
  | 0, _ => rfl
  | r + 1, i => by
    rw [omissionQuorum_state_succ]; simp only [omissionUpdate]
    split <;> split <;> (try split_ifs) <;> exact omissionState_input_eq deliver x r i

private theorem omission_decided_unchanged_of_ne_two (deliver : ℕ → P → P → Bool) (x : P → V)
    (r : ℕ) (h : r % 3 ≠ 2) (i : P) :
    ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (r + 1) i).decided =
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).decided := by
  rw [omissionQuorum_state_succ]
  rcases (by omega : r % 3 = 0 ∨ r % 3 = 1) with h | h <;> simp only [omissionUpdate, h]
  split <;> (try split_ifs) <;> rfl

/-- Decisions of `omissionQuorumProtocol` are write-once across all rounds. -/
theorem omission_irrevocable (deliver : ℕ → P → P → Bool) (x : P → V)
    {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) (i : P) (val : V)
    (hdec : (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₁ i =
      some val) :
    (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₂ i = some val := by
  induction hr with
  | refl => exact hdec
  | @step m _ ih =>
    by_cases hm2 : m % 3 = 2
    · rw [PartialSyncProtocol.omissionDecision, omissionQuorum_state_succ]
      simp only [omissionUpdate, hm2]
      split
      · next w _ => exact congrArg (Option.or · (some w)) ih
      · exact ih
    · exact (omission_decided_unchanged_of_ne_two leader deliver x m hm2 i).trans ih

theorem omission_locked_unchanged_of_ne_one (deliver : ℕ → P → P → Bool) (x : P → V)
    (r : ℕ) (h : r % 3 ≠ 1) (i : P) :
    ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (r + 1) i).locked =
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).locked := by
  rw [omissionQuorum_state_succ]
  rcases (by omega : r % 3 = 0 ∨ r % 3 = 2) with h | h <;> simp only [omissionUpdate, h]
  split <;> rfl

/-- Any lock `some lk` held at round `r` of `omissionQuorumProtocol` satisfies `3 * lk.view + 1 < r`
and equals the coordinator's `leaderProposal` at `3 * lk.view + 1`. -/
private theorem omissionState_locked_origin (deliver : ℕ → P → P → Bool) (x : P → V) :
    ∀ r i {lk : ViewLock V},
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).locked = some lk →
      3 * lk.view + 1 < r ∧
        ∃ cv, ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x (3 * lk.view + 1) (leader lk.view)).leaderProposal = some ⟨lk.val, cv⟩
  | 0, _, _, hlk => by
    simp only [PartialSyncProtocol.omissionState, omissionQuorumProtocol, reduceCtorEq] at hlk
  | r + 1, i, lk, hlk => by
    by_cases hkeep :
        ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).locked = some lk
    · obtain ⟨hlt, hprop⟩ := omissionState_locked_origin deliver x r i hkeep
      exact ⟨by omega, hprop⟩
    have hr1 : r % 3 = 1 := by_contra fun hr1 =>
      hkeep (by rwa [omission_locked_unchanged_of_ne_one leader deliver x r hr1 i] at hlk)
    rw [omissionQuorum_state_succ] at hlk
    simp only [omissionUpdate, hr1] at hlk
    split at hlk
    · next v' prop hm =>
      split_ifs at hlk
      · cases hlk
        dsimp only
        -- The accepted proposal is the coordinator's `leaderProposal` from round `r`.
        cases hdel : deliver r (leader (r / 3)) i <;>
          simp only [omissionIncoming, hdel, ↓reduceIte, Bool.false_eq_true, omissionSend, hr1,
            reduceCtorEq] at hm
        split at hm
        · next prop' hlp =>
          simp only [Option.some.injEq, OmissionViewMsg.propose.injEq] at hm
          refine ⟨by omega, prop.certView, ?_⟩
          rw [show 3 * (r / 3) + 1 = r by omega, hlp, hm.2]
        · simp only [Option.some.injEq, reduceCtorEq] at hm
      · exact absurd hlk hkeep
    · exact absurd hlk hkeep

private theorem omission_first_decision (deliver : ℕ → P → P → Bool) (x : P → V) :
    ∀ r i {val : V},
      (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r i = some val →
      ∃ m < r,
        ((omissionQuorumProtocol P V procs leader t).omissionState deliver x m i).decided = none ∧
        ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x (m + 1) i).decided = some val
  | 0, _, _, h => by
    simp only [PartialSyncProtocol.omissionDecision, PartialSyncProtocol.omissionState,
      omissionQuorumProtocol, reduceCtorEq] at h
  | r + 1, i, val, h => by
    cases hprev : ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x r i).decided with
    | none => exact ⟨r, Nat.lt_succ_self r, hprev, h⟩
    | some w =>
      obtain rfl := Option.some.inj
        ((omission_irrevocable leader deliver x r.le_succ i w hprev).symm.trans h)
      exact (omission_first_decision deliver x r i hprev).imp fun _ hm =>
        ⟨Nat.lt_succ_of_lt hm.1, hm.2⟩

private theorem omission_decision_step_quorum [Fintype P] (hprocs : ∀ p : P, p ∈ procs)
    (hn : 2 * t < Fintype.card P) (deliver : ℕ → P → P → Bool) (x : P → V)
    {r : ℕ} {i : P} {val₀ : V}
    (hnone : ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).decided =
      none)
    (hsome : ((omissionQuorumProtocol P V procs leader t).omissionState
      deliver x (r + 1) i).decided = some val₀) :
    r % 3 = 2 ∧
      Fintype.card P - t ≤
        (Finset.univ.filter fun q =>
          ((omissionQuorumProtocol P V procs leader t).omissionState
            deliver x (r + 1) q).locked = some ⟨r / 3, val₀⟩).card := by
  have hr2 : r % 3 = 2 := by_contra fun hne => by
    simp [omission_decided_unchanged_of_ne_two leader deliver x r hne i, hnone] at hsome
  refine ⟨hr2, ?_⟩
  rw [omissionQuorum_state_succ] at hsome
  simp only [omissionUpdate, hr2] at hsome
  split at hsome
  · next w hfq =>
    simp only [hnone, Option.none_or, Option.some.injEq] at hsome
    subst hsome
    refine le_trans (findQuorumVal_dedup_sub hprocs (by omega) _ hfq)
      (Finset.card_le_card fun q hq => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [omission_locked_unchanged_of_ne_one leader deliver x r (by omega) q]
    -- `q` acknowledged `w`, so it locked `⟨r / 3, w⟩` on accepting a proposal in Subround 1.
    cases hdel : deliver r q i <;>
      simp only [omissionIncoming, hdel, ↓reduceIte, Bool.false_eq_true, omissionSend, hr2,
        extractAck, reduceCtorEq] at hq
    cases hma : ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r q).myAck <;>
      simp only [hma, ↓reduceIte, Option.some.injEq, reduceCtorEq] at hq
    subst hq
    obtain ⟨v, rfl⟩ : ∃ v, r = 3 * v + 1 + 1 := ⟨r / 3, by omega⟩
    rw [omissionQuorum_state_succ] at hma ⊢
    simp only [omissionUpdate, show (3 * v + 1) % 3 = 1 by omega,
      show (3 * v + 1) / 3 = v by omega, show (3 * v + 1 + 1) / 3 = v by omega] at hma ⊢
    split at hma
    · split_ifs at hma ⊢
      cases hma; rfl
    · cases hma
  · simp only [hnone, reduceCtorEq] at hsome

private theorem extractStatusLock_incoming_locked (deliver : ℕ → P → P → Bool) (x : P → V)
    {v : ℕ} {jb : P} {best : ViewLock V}
    (hjb : extractStatusLock (omissionIncoming procs leader t deliver x (3 * v) (leader v) jb) =
      some best) :
    best.view < v ∧
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (3 * v) jb).locked =
        some best := by
  cases hdel : deliver (3 * v) jb (leader v) <;>
    simp only [omissionIncoming, hdel, ↓reduceIte, Bool.false_eq_true, omissionSend,
      show 3 * v % 3 = 0 by omega, extractStatusLock, reduceCtorEq] at hjb
  cases hjblk : ((omissionQuorumProtocol P V procs leader t).omissionState
      deliver x (3 * v) jb).locked with
  | none => simp only [hjblk, reduceCtorEq] at hjb
  | some lk_b =>
    simp only [hjblk, Option.some.injEq] at hjb
    subst hjb
    have := (omissionState_locked_origin leader deliver x (3 * v) jb hjblk).1
    exact ⟨by omega, rfl⟩

private theorem omission_lock_preservation [Fintype P] (hprocs : ∀ p : P, p ∈ procs)
    (hn : 2 * t < Fintype.card P) (deliver : ℕ → P → P → Bool) (x : P → V)
    {v₀ : ℕ} {val₀ : V} {Q₀ : Finset P}
    (hQ₀_card : Fintype.card P - t ≤ Q₀.card)
    (hQ₀_lock : ∀ q ∈ Q₀, ((omissionQuorumProtocol P V procs leader t).omissionState
      deliver x (3 * (v₀ + 1)) q).locked = some ⟨v₀, val₀⟩) :
    ∀ d : ℕ,
      (∀ r p val, ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x r p).locked = some ⟨v₀ + d, val⟩ → val = val₀) ∧
      (∀ q ∈ Q₀, ∃ u_q, v₀ ≤ u_q ∧
        ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x (3 * (v₀ + d + 1)) q).locked = some ⟨u_q, val₀⟩) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    have hv_lock : ∀ r p val, ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x r p).locked = some ⟨v₀ + d, val⟩ → val = val₀ := by
      intro r p val hlk
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · obtain ⟨q₀, hq₀⟩ := Finset.card_pos.1 (by omega : 0 < Q₀.card)
        obtain ⟨_, cv₁, hp₁⟩ := omissionState_locked_origin leader deliver x r p hlk
        obtain ⟨_, cv₂, hp₂⟩ :=
          omissionState_locked_origin leader deliver x _ q₀ (hQ₀_lock q₀ hq₀)
        exact congrArg Proposal.val (Option.some.inj (hp₁.symm.trans hp₂))
      obtain ⟨_, cv, hlp⟩ := omissionState_locked_origin leader deliver x r p hlk
      dsimp only at hlp
      set v := v₀ + d
      rw [omissionQuorum_state_succ] at hlp
      simp only [omissionUpdate, show 3 * v % 3 = 0 by omega] at hlp
      split_ifs at hlp with hcnt
      rw [dedup_length_eq_card hprocs, length_filter_dedup_eq_card hprocs] at hcnt
      -- Some `qStar ∈ Q₀` reported its lock `⟨u_q, val₀⟩` (`v₀ ≤ u_q`) to the coordinator.
      obtain ⟨qStar, hqInter, -⟩ := quorum_inter_notMem (F := ∅)
        (S₁ := Finset.univ.filter fun j =>
          isOmissionStatus (omissionIncoming procs leader t deliver x (3 * v) (leader v) j) =
            true)
        (S₂ := Q₀) (by simp only [Finset.card_empty]; omega)
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hqInter
      obtain ⟨hqS, hqQ₀⟩ := hqInter
      obtain ⟨u_q, hu_ge, hqlk⟩ := (ih (d - 1) (by omega)).2 qStar hqQ₀
      rw [show v₀ + (d - 1) + 1 = v by omega] at hqlk
      have hmem_locks : (⟨u_q, val₀⟩ : ViewLock V) ∈ procs.dedup.filterMap fun j =>
          extractStatusLock (omissionIncoming procs leader t deliver x (3 * v) (leader v) j) := by
        refine List.mem_filterMap.2 ⟨qStar, List.mem_dedup.2 (hprocs qStar), ?_⟩
        cases hdel : deliver (3 * v) qStar (leader v) <;>
          simp only [omissionIncoming, hdel, ↓reduceIte, Bool.false_eq_true, omissionSend,
            show 3 * v % 3 = 0 by omega, isOmissionStatus, hqlk, extractStatusLock] at hqS ⊢
      -- The coordinator proposed the maximal reported lock, held by `jb` from a view in `[v₀, v)`.
      split at hlp
      · next best hpm =>
        simp only [Option.some.injEq, Proposal.mk.injEq] at hlp
        obtain ⟨jb, -, hjb⟩ := List.mem_filterMap.1 (pickMaxLock_mem hpm)
        obtain ⟨hlt_b, hjblk⟩ := extractStatusLock_incoming_locked leader deliver x hjb
        have hbest_ge : v₀ ≤ best.view := hu_ge.trans (pickMaxLock_le hpm _ hmem_locks)
        refine hlp.1.symm.trans ((ih (best.view - v₀) (by omega)).1 (3 * v) jb best.val ?_)
        rwa [show v₀ + (best.view - v₀) = best.view by omega]
      · next hpm =>
        simp [pickMaxLock_eq_none_iff.1 hpm] at hmem_locks
    refine ⟨hv_lock, fun q hq => ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · exact ⟨v₀, le_rfl, hQ₀_lock q hq⟩
    set v := v₀ + d
    obtain ⟨u_prev, hu_prev, hlk_prev⟩ := (ih (d - 1) (by omega)).2 q hq
    rw [show v₀ + (d - 1) + 1 = v by omega] at hlk_prev
    rw [show 3 * (v + 1) = 3 * v + 1 + 1 + 1 by omega,
      omission_locked_unchanged_of_ne_one leader deliver x _ (by omega)]
    by_cases hkeep : ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x (3 * v + 1 + 1) q).locked =
        ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (3 * v + 1) q).locked
    · rw [hkeep, omission_locked_unchanged_of_ne_one leader deliver x _ (by omega)]
      exact ⟨u_prev, hu_prev, hlk_prev⟩
    -- Otherwise `q` locked a fresh view-`v` value, which must be `val₀`.
    obtain ⟨w, hw⟩ : ∃ w, ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x (3 * v + 1 + 1) q).locked = some ⟨v, w⟩ := by
      rw [omissionQuorum_state_succ] at hkeep ⊢
      simp only [omissionUpdate, show (3 * v + 1) % 3 = 1 by omega,
        show (3 * v + 1) / 3 = v by omega] at hkeep ⊢
      split at hkeep <;> (try split_ifs at hkeep ⊢)
      exacts [⟨_, rfl⟩, (hkeep rfl).elim, (hkeep rfl).elim]
    exact ⟨v, by omega, by rw [hw, hv_lock _ q w hw]⟩

private theorem omission_decided_quorum_view [Fintype P] (hprocs : ∀ p : P, p ∈ procs)
    (hn : 2 * t < Fintype.card P) (deliver : ℕ → P → P → Bool) (x : P → V)
    {r : ℕ} {i : P} {v : V}
    (hdec : (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r i = some v) :
    ∃ (u : ℕ) (Q : Finset P) (q : P),
      Fintype.card P - t ≤ Q.card ∧
      (∀ p ∈ Q, ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x (3 * (u + 1)) p).locked = some ⟨u, v⟩) ∧
      ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x (3 * (u + 1)) q).locked = some ⟨u, v⟩ := by
  obtain ⟨m, -, hmn, hms⟩ := omission_first_decision leader deliver x r i hdec
  obtain ⟨hr2, hQ⟩ := omission_decision_step_quorum leader hprocs hn deliver x hmn hms
  let u := m / 3
  have hm1 : m + 1 = 3 * (u + 1) := by omega
  rw [hm1] at hQ
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hQ)
  exact ⟨u, _, q, hQ, fun p hp => (Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hq).2⟩

/-- **Unconditional pre-GST agreement for `omissionQuorumProtocol` (`omission_agreement`):**
when `2 * t < Fintype.card P`, no two processes ever decide distinct values (even without `GST`). -/
theorem omission_agreement [Fintype P] (hprocs : ∀ p : P, p ∈ procs)
    (hn : 2 * t < Fintype.card P) (deliver : ℕ → P → P → Bool) (x : P → V)
    {r₁ r₂ : ℕ} {i j : P} {v₁ v₂ : V}
    (h₁ : (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₁ i = some v₁)
    (h₂ : (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₂ j = some v₂) :
    v₁ = v₂ := by
  obtain ⟨u₁, Q₁, q₁, hQ₁, hlkQ₁, hq₁⟩ :=
    omission_decided_quorum_view leader hprocs hn deliver x h₁
  obtain ⟨u₂, Q₂, q₂, hQ₂, hlkQ₂, hq₂⟩ :=
    omission_decided_quorum_view leader hprocs hn deliver x h₂
  rcases le_total u₁ u₂ with hle | hle
  · exact ((omission_lock_preservation leader hprocs hn deliver x hQ₁ hlkQ₁ (u₂ - u₁)).1
      (3 * (u₂ + 1)) q₂ v₂ (by rw [Nat.add_sub_of_le hle]; exact hq₂)).symm
  · exact (omission_lock_preservation leader hprocs hn deliver x hQ₂ hlkQ₂ (u₁ - u₂)).1
      (3 * (u₁ + 1)) q₁ v₁ (by rw [Nat.add_sub_of_le hle]; exact hq₁)

/-- **Unconditional strong unanimity for `omissionQuorumProtocol` (`omission_validity`):** when
`2 * t < Fintype.card P` and all initial inputs equal `val₀` (`∀ i, x i = val₀`), no process ever
decides any value other than `val₀` (even without `GST`). -/
theorem omission_validity [Fintype P] (hprocs : ∀ p : P, p ∈ procs)
    (hn : 2 * t < Fintype.card P) (deliver : ℕ → P → P → Bool)
    {x : P → V} {val₀ : V} (hx : ∀ p, x p = val₀) :
    ∀ r i {w : V},
      (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r i = some w →
      w = val₀ := by
  have hlock_val : ∀ u r p w,
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r p).locked =
        some ⟨u, w⟩ → w = val₀ := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro r p w hlk
      obtain ⟨_, cv, hlp⟩ := omissionState_locked_origin leader deliver x r p hlk
      dsimp only at hlp
      rw [omissionQuorum_state_succ] at hlp
      simp only [omissionUpdate, Nat.mul_mod_right] at hlp
      split_ifs at hlp with hcnt
      split at hlp <;> simp only [Option.some.injEq, Proposal.mk.injEq] at hlp
      · next best hpm =>
        obtain ⟨jb, -, hjb⟩ := List.mem_filterMap.1 (pickMaxLock_mem hpm)
        obtain ⟨hlt_b, hjblk⟩ := extractStatusLock_incoming_locked leader deliver x hjb
        exact hlp.1.symm.trans (ih best.view hlt_b (3 * u) jb best.val hjblk)
      · rw [← hlp.1, omissionState_input_eq, hx]
  intro r i w hdec
  obtain ⟨u, _, q, -, -, hq⟩ := omission_decided_quorum_view leader hprocs hn deliver x hdec
  exact hlock_val u (3 * (u + 1)) q w hq

end OmissionSafety

end Cslib.Distributed.PartialSynchrony
