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
    have heq₁ := congrArg (π.output i) (π.omissionState_eq_byzantineState ∅ deliver x r₁ i)
    have heq₂ := congrArg (π.output i) (π.omissionState_eq_byzantineState ∅ deliver x r₂ i)
    exact heq₂.trans (h.irrevocable ∅ (Nat.zero_le t) deliver _ x r₁ r₂ hr i
      (Finset.notMem_empty i) v (heq₁.symm.trans hdec))
  agreement F hF deliver x r₁ r₂ i hi j hj v₁ v₂ h₁ h₂ := by
    have heq₁ := congrArg (π.output i) (π.omissionState_eq_byzantineState F deliver x r₁ i)
    have heq₂ := congrArg (π.output j) (π.omissionState_eq_byzantineState F deliver x r₂ j)
    exact h.agreement F hF deliver _ x r₁ r₂ i hi j hj v₁ v₂
      (heq₁.symm.trans h₁) (heq₂.symm.trans h₂)
  validity deliver x v hv r i w hdec := by
    have heq := congrArg (π.output i) (π.omissionState_eq_byzantineState ∅ deliver x r i)
    exact h.validity ∅ (Nat.zero_le t) deliver _ x v (fun j _ => hv j) r i
      (Finset.notMem_empty i) w (heq.symm.trans hdec)
  termination F hF deliver gst x hgst i hi := by
    obtain ⟨r, hr⟩ := h.termination F hF deliver gst (π.omissionAdv deliver x) x hgst i hi
    refine ⟨r, ?_⟩
    change (π.output i (π.omissionState deliver x r i)).isSome = true
    rw [π.omissionState_eq_byzantineState F deliver x r i]
    exact hr

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
    change some ((ownInputProtocol P V).byzantineState F deliver adv x r₁ i) = some v at h₁
    change some ((ownInputProtocol P V).byzantineState F deliver adv x r₂ i) = some v
    rw [ownInputProtocol_byzantineState] at h₁ ⊢
    exact h₁
  agreement F _ deliver adv x r₁ r₂ i _ j _ v₁ v₂ h₁ h₂ := by
    change some ((ownInputProtocol P V).byzantineState F deliver adv x r₁ i) = some v₁ at h₁
    change some ((ownInputProtocol P V).byzantineState F deliver adv x r₂ j) = some v₂ at h₂
    rw [ownInputProtocol_byzantineState, Option.some.injEq] at h₁ h₂
    rw [← h₁, ← h₂, Subsingleton.elim i j]
  validity F _ deliver adv x v hv r i hi w hw := by
    change some ((ownInputProtocol P V).byzantineState F deliver adv x r i) = some w at hw
    rw [ownInputProtocol_byzantineState, Option.some.injEq] at hw
    rw [← hw, hv i hi]
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
  have hnd : (procs.dedup.filter p).Nodup := List.Nodup.filter _ (List.nodup_dedup procs)
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, List.mem_dedup, hprocs x, true_and,
    Finset.mem_filter, Finset.mem_univ]

/-- When `procs` enumerates `P`, `procs.dedup.length = Fintype.card P`. -/
theorem dedup_length_eq_card {P : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) :
    procs.dedup.length = Fintype.card P := by
  have h := length_filter_dedup_eq_card hprocs (fun _ => true)
  simpa using h

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
  simp only [findQuorumVal, List.findSome?_eq_some_iff] at h
  obtain ⟨_, j, _, _, hj, _⟩ := h
  cases hfj : f j with
  | none => simp only [hfj, reduceCtorEq] at hj
  | some w =>
    simp only [hfj] at hj
    split_ifs at hj with hq
    simp only [Option.some.injEq] at hj
    subst hj
    exact hq

/-- When `Fintype.card P < 2 * q`, at most one value can have `q` senders, so `findQuorumVal`
returns `some v` if and only if at least `q` senders carry `some v`. -/
theorem findQuorumVal_eq_some_iff {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {procs : List P} (hprocs : ∀ x : P, x ∈ procs) {q : ℕ} (hq : Fintype.card P < 2 * q)
    (f : P → Option V) (v : V) :
    findQuorumVal procs q f = some v ↔
      q ≤ (Finset.univ.filter fun j => f j = some v).card := by
  have huniq : ∀ v₁ v₂,
      q ≤ (Finset.univ.filter fun j => f j = some v₁).card →
      q ≤ (Finset.univ.filter fun j => f j = some v₂).card → v₁ = v₂ := by
    intro v₁ v₂ h₁ h₂
    obtain ⟨j, hj, -⟩ := quorum_inter_notMem (F := ∅)
      (S₁ := Finset.univ.filter fun j => f j = some v₁)
      (S₂ := Finset.univ.filter fun j => f j = some v₂)
      (by simp only [Finset.card_empty]; omega)
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Option.some.inj (hj.1.symm.trans hj.2)
  constructor
  · intro h
    have hc := findQuorumVal_sound h
    rwa [countVal_eq_card hprocs] at hc
  · intro hv
    have hne : (Finset.univ.filter fun j => f j = some v).Nonempty :=
      Finset.card_pos.1 (by omega)
    obtain ⟨j₀, hj₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀
    have hnone : findQuorumVal procs q f ≠ none := by
      intro hn
      simp only [findQuorumVal, List.findSome?_eq_none_iff] at hn
      have hj := hn j₀ (List.mem_dedup.2 (hprocs j₀))
      have hcv : q ≤ countVal procs f v := by rwa [countVal_eq_card hprocs]
      simp only [hj₀, hcv, ↓reduceIte, reduceCtorEq] at hj
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hnone
    have hwc := findQuorumVal_sound hw
    rw [countVal_eq_card hprocs] at hwc
    rw [hw, huniq w v hwc hv]

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
  have e₁ := h₁_honest h hhF v₁ hh.1
  have e₂ := h₂_honest h hhF v₂ hh.2
  exact Option.some.inj (e₁.symm.trans e₂)

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
  induction lks with
  | nil => simp only [pickMaxLock]
  | cons lk lks _ =>
    simp only [pickMaxLock, reduceCtorEq, iff_false]
    cases pickMaxLock lks with
    | none => simp only [reduceCtorEq, not_false_eq_true]
    | some best =>
      by_cases hle : best.view ≤ lk.view <;> simp [hle]

theorem pickMaxLock_mem {V : Type*} {lks : List (ViewLock V)} {best : ViewLock V}
    (h : pickMaxLock lks = some best) : best ∈ lks := by
  induction lks generalizing best with
  | nil => simp only [pickMaxLock, reduceCtorEq] at h
  | cons lk lks ih =>
    simp only [pickMaxLock] at h
    cases hrec : pickMaxLock lks with
    | none =>
      rw [hrec] at h
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | some b =>
      rw [hrec] at h
      by_cases hle : b.view ≤ lk.view
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact List.mem_cons_of_mem lk (ih hrec)

theorem pickMaxLock_le {V : Type*} {lks : List (ViewLock V)} {best : ViewLock V}
    (h : pickMaxLock lks = some best) : ∀ lk ∈ lks, lk.view ≤ best.view := by
  induction lks generalizing best with
  | nil => simp only [pickMaxLock, reduceCtorEq] at h
  | cons hd tl ih =>
    intro lk hlk
    simp only [pickMaxLock] at h
    cases hrec : pickMaxLock tl with
    | none =>
      rw [hrec] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [pickMaxLock_eq_none_iff.1 hrec] at hlk
      simp only [List.mem_singleton] at hlk
      subst hlk
      exact le_rfl
    | some b =>
      rw [hrec] at h
      have htl := ih hrec
      rcases List.mem_cons.1 hlk with rfl | hmem
      · by_cases hle : b.view ≤ lk.view
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h; exact le_rfl
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h; omega
      · have hb := htl lk hmem
        by_cases hle : b.view ≤ hd.view
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h; omega
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h; subst h; exact hb

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
    simp only [List.filterMap_cons, List.filter_cons]
    cases f a with
    | none => simp only [Option.map_none, ↓reduceIte, Bool.false_eq_true, ih]
    | some p =>
      simp only [Option.map_some, List.filter_cons]
      by_cases hp : pred p.1 <;> simp [hp, ih]

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
    have ih := byzState_input_eq F deliver adv x r i
    rw [byzQuorum_state_succ]
    simp only [byzUpdate]
    have hmod : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ r % 6 = 3 ∨ r % 6 = 4 ∨ r % 6 = 5 := by omega
    rcases hmod with h0 | h1 | h2 | h3 | h4 | h5
    · simp only [h0]; exact ih
    · simp only [h1]; exact ih
    · simp only [h2]; exact ih
    · simp only [h3]; cases findQuorumVal (V := V) procs _ _ <;> exact ih
    · simp only [h4]; cases findQuorumVal (V := V) procs _ _ <;> exact ih
    · simp only [h5]; cases findQuorumVal (V := V) procs _ _ <;> exact ih

private theorem byzState_decided_unchanged_of_ne_five (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 5) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).decided =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).decided := by
  rw [byzQuorum_state_succ]
  simp only [byzUpdate]
  have hmod : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ (r % 6 = 3 ∨ r % 6 = 4) := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · simp only [h0]
  · simp only [h1]
  · simp only [h2]
  · simp only [h3]; cases findQuorumVal (V := V) procs _ _ <;> rfl
  · simp only [h4]; cases findQuorumVal (V := V) procs _ _ <;> rfl

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
    change ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x m i).decided =
      some val at ih
    change ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (m + 1) i).decided = some val
    by_cases hm5 : m % 6 = 5
    · rw [byzQuorum_state_succ]
      simp only [byzUpdate, hm5]
      cases findQuorumVal (V := V) procs _ _ with
      | none => exact ih
      | some w => simp only [ih, Option.some_or]
    · rw [byzState_decided_unchanged_of_ne_five leader F deliver adv x m hm5 i]
      exact ih

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
    rw [byzQuorum_state_succ]
    simp only [byzUpdate]
    have hmod : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
    rcases hmod with h0 | h1 | h2 | h3 | h4 | h5
    · simp only [h0]; exact ih
    · simp only [h1]; exact ih
    · simp only [h2]; exact ih
    · simp only [h3]
      cases findQuorumVal (V := V) procs _ _ with
      | none => exact ih
      | some w =>
        by_cases hm : (⟨m / 6, w⟩ : ViewLock V) ∈
            ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x m i).votedViews
        · simp only [hm, ↓reduceIte]; exact ih
        · simp only [hm, ↓reduceIte]; exact List.mem_cons_of_mem _ ih
    · simp only [h4]; cases findQuorumVal (V := V) procs _ _ <;> exact ih
    · simp only [h5]; cases findQuorumVal (V := V) procs _ _ <;> exact ih

private theorem byzState_votedViews_unchanged_of_ne_three (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 3) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).votedViews =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).votedViews := by
  rw [byzQuorum_state_succ]
  simp only [byzUpdate]
  have hmod : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ r % 6 = 4 ∨ r % 6 = 5 := by omega
  rcases hmod with h0 | h1 | h2 | h4 | h5
  · simp only [h0]
  · simp only [h1]
  · simp only [h2]
  · simp only [h4]; cases findQuorumVal (V := V) procs _ _ <;> rfl
  · simp only [h5]; cases findQuorumVal (V := V) procs _ _ <;> rfl

theorem byzState_locked_unchanged_of_ne_four (F : Finset P)
    (deliver : ℕ → P → P → Bool) (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V)
    (r : ℕ) (h : r % 6 ≠ 4) (i : P) :
    ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (r + 1) i).locked =
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).locked := by
  rw [byzQuorum_state_succ]
  simp only [byzUpdate]
  have hmod : r % 6 = 0 ∨ r % 6 = 1 ∨ r % 6 = 2 ∨ r % 6 = 3 ∨ r % 6 = 5 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h5
  · simp only [h0]
  · simp only [h1]
  · simp only [h2]
  · simp only [h3]; cases findQuorumVal (V := V) procs _ _ <;> rfl
  · simp only [h5]; cases findQuorumVal (V := V) procs _ _ <;> rfl

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
      cases hfq : findQuorumVal procs (procs.dedup.length - t)
          (fun j => extractEcho (r / 6) (byzIncoming procs leader t F deliver adv x r i j)) with
      | none =>
        rw [hfq] at hlk
        obtain ⟨hlt, hq⟩ := votedViews_origin hprocs hn r i hlk
        exact ⟨by omega, hq⟩
      | some val =>
        rw [hfq] at hlk
        by_cases hmem : (⟨r / 6, val⟩ : ViewLock V) ∈
            ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r i).votedViews
        · simp only [hmem, ↓reduceIte] at hlk
          obtain ⟨hlt, hq⟩ := votedViews_origin hprocs hn r i hlk
          exact ⟨by omega, hq⟩
        · simp only [hmem, ↓reduceIte] at hlk
          rcases List.mem_cons.1 hlk with rfl | hold
          · dsimp only
            have hr_eq : 6 * (r / 6) + 3 = r := by omega
            refine ⟨by omega, ?_⟩
            simpa only [hr_eq] using findQuorumVal_dedup_sub hprocs (by omega) _ hfq
          · obtain ⟨hlt, hq⟩ := votedViews_origin hprocs hn r i hold
            exact ⟨by omega, hq⟩
    · rw [byzState_votedViews_unchanged_of_ne_three leader F deliver adv x r hr3 i] at hlk
      obtain ⟨hlt, hq⟩ := votedViews_origin hprocs hn r i hlk
      exact ⟨by omega, hq⟩

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
    v₁ = v₂ := by
  obtain ⟨_, hq₁⟩ := votedViews_origin leader hprocs hn r₁ i₁ h₁
  obtain ⟨_, hq₂⟩ := votedViews_origin leader hprocs hn r₂ i₂ h₂
  let st3 := (byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x (6 * u + 3)
  let mAt (i j : P) : Option V :=
    extractEcho u (byzIncoming procs leader t F deliver adv x (6 * u + 3) i j)
  have hhonest : ∀ i, ∀ h ∉ F, ∀ w, mAt i h = some w → (st3 h).myEcho = some w := by
    intro i h hhF w hw
    simp only [mAt, byzIncoming, hhF, ↓reduceIte] at hw
    cases hdel : deliver (6 * u + 3) h i
    · rw [hdel] at hw; simp only [Bool.false_eq_true, ↓reduceIte, extractEcho, reduceCtorEq] at hw
    · rw [hdel] at hw
      simp only [↓reduceIte, byzSend, show (6 * u + 3) / 6 = u by omega,
        show (6 * u + 3) % 6 = 3 by omega] at hw
      cases he : (st3 h).myEcho with
      | none => rw [he] at hw; simp only [extractEcho, reduceCtorEq] at hw
      | some w' =>
        rw [he] at hw
        simp only [extractEcho, ↓reduceIte, Option.some.injEq] at hw
        rw [hw]
  exact prevoteQuorum_unique hn hF (honestEcho := fun h => (st3 h).myEcho)
    (hhonest i₁) (hhonest i₂) hq₁ hq₂

/-- Soundness of Subround-0 `certPairs`: if `lk ∈ certPairs` after Subround 0 of view `v`,
then `lk.view < v` and some correct process `h ∉ F` already held `lk ∈ votedViews` at `6 * v`. -/
private theorem certPairs_sound {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    (hF : F.card ≤ t) (v : ℕ) (i : P) {lk : ViewLock V}
    (hlk : lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v + 1) i).certPairs) :
    lk.view < v ∧ ∃ h ∉ F, lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v) h).votedViews := by
  rw [show 6 * v + 1 = (6 * v) + 1 by rfl, byzQuorum_state_succ] at hlk
  simp only [byzUpdate, show (6 * v) % 6 = 0 by omega, show (6 * v) / 6 = v by omega,
    computeCertPairs, List.mem_filter, decide_eq_true_eq, rawVoteCount] at hlk
  rcases hlk with ⟨_, hcnt⟩
  split_ifs at hcnt with hlt
  · have hnd : (procs.dedup.filter fun j =>
        decide (lk ∈ extractRawVotes
          (byzIncoming procs leader t F deliver adv x (6 * v) i j))).Nodup :=
      List.Nodup.filter _ (List.nodup_dedup procs)
    rw [← List.toFinset_card_of_nodup hnd] at hcnt
    obtain ⟨h, hh, hhF⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hF hcnt)
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, byzIncoming, hhF,
      ↓reduceIte] at hh
    rcases hh with ⟨_, hh⟩
    cases hdel : deliver (6 * v) h i
    · rw [hdel] at hh
      simp only [Bool.false_eq_true, ↓reduceIte, extractRawVotes, List.not_mem_nil] at hh
    · rw [hdel] at hh
      simp only [↓reduceIte, byzSend, show (6 * v) % 6 = 0 by omega, extractRawVotes] at hh
      exact ⟨hlt, h, hhF, hh⟩
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
  rw [show 6 * v + 2 = (6 * v + 1) + 1 by omega, byzQuorum_state_succ] at hlk
  have hm1 : (6 * v + 1) % 6 = 1 := by omega
  have hd1 : (6 * v + 1) / 6 = v := by omega
  simp only [byzUpdate, hm1, hd1, List.mem_filter, decide_eq_true_eq, certSupportCount] at hlk
  rcases hlk with ⟨_, hcnt⟩
  split_ifs at hcnt with hlt
  · have hnd : (procs.dedup.filter fun j =>
        match extractCertStatus (byzIncoming procs leader t F deliver adv x (6 * v + 1) i j) with
        | some (_, cp) => decide (lk ∈ cp)
        | none => false).Nodup :=
      List.Nodup.filter _ (List.nodup_dedup procs)
    rw [← List.toFinset_card_of_nodup hnd] at hcnt
    obtain ⟨r, hr, hrF⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hF hcnt)
    simp only [List.mem_toFinset, List.mem_filter, byzIncoming, hrF, ↓reduceIte] at hr
    rcases hr with ⟨_, hr⟩
    cases hdel : deliver (6 * v + 1) r i
    · rw [hdel] at hr
      simp only [Bool.false_eq_true, ↓reduceIte, extractCertStatus, Bool.false_eq_true] at hr
    · rw [hdel] at hr
      simp only [↓reduceIte, byzSend, hm1, extractCertStatus, decide_eq_true_eq] at hr
      exact certPairs_sound leader hF v r hr
  · omega

private theorem byzIncoming_honest_deliver {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    {r : ℕ} {i h : P} (hhF : h ∉ F) {g : Option (ByzViewMsg V) → Option V}
    (hnone : g none = none) {w : V}
    (hg : g (byzIncoming procs leader t F deliver adv x r i h) = some w) :
    g (some (byzSend leader r h
      ((byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x r h))) = some w := by
  simp only [byzIncoming, hhF, ↓reduceIte] at hg
  cases hdel : deliver r h i
  · rw [hdel] at hg
    simp only [Bool.false_eq_true, ↓reduceIte, hnone, reduceCtorEq] at hg
  · rw [hdel] at hg
    simpa only [↓reduceIte] using hg

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
    by_cases hr4 : r % 6 = 4
    · rw [byzQuorum_state_succ] at hlk
      simp only [byzUpdate, hr4] at hlk
      cases hfq : findQuorumVal procs (procs.dedup.length - t)
          (fun j => extractVote (r / 6) (byzIncoming procs leader t F deliver adv x r i j)) with
      | none =>
        rw [hfq] at hlk
        obtain ⟨hlt, hcard⟩ := byzState_locked_witness hprocs hn hF r i hlk
        refine ⟨by omega, le_trans hcard (Finset.card_le_card fun h hh => ?_)⟩
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh ⊢
        exact ⟨hh.1, byzState_votedViews_mono leader F deliver adv x (Nat.le_succ r) h hh.2⟩
      | some val =>
        rw [hfq] at hlk
        simp only [Option.some.injEq] at hlk
        subst hlk
        have hiff := findQuorumVal_dedup_sub hprocs (by omega) _ hfq
        have hsub : (Finset.univ.filter fun j =>
            extractVote (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some val) \ F ⊆
            (Finset.univ \ F).filter fun h =>
              (⟨r / 6, val⟩ : ViewLock V) ∈
                ((byzQuorumProtocol P V procs leader t).byzantineState
                  F deliver adv x (r + 1) h).votedViews := by
          intro h hh
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
          rcases hh with ⟨hhv, hhF⟩
          refine ⟨hhF, ?_⟩
          have hhv' := byzIncoming_honest_deliver leader hhF rfl hhv
          simp only [byzSend, hr4] at hhv'
          have hr3_eq : r = (6 * (r / 6) + 3) + 1 := by omega
          cases hmv : ((byzQuorumProtocol P V procs leader t).byzantineState
              F deliver adv x r h).myVote with
          | none => rw [hmv] at hhv'; simp only [extractVote, reduceCtorEq] at hhv'
          | some w =>
            rw [hmv] at hhv'
            simp only [extractVote, ↓reduceIte, Option.some.injEq] at hhv'
            subst hhv'
            refine byzState_votedViews_mono leader F deliver adv x (Nat.le_succ r) h ?_
            rw [hr3_eq, byzQuorum_state_succ] at hmv ⊢
            have hm3 : (6 * (r / 6) + 3) % 6 = 3 := by omega
            have hd3 : (6 * (r / 6) + 3) / 6 = r / 6 := by omega
            simp only [byzUpdate, hm3, hd3] at hmv ⊢
            cases hfq3 : findQuorumVal (V := V) procs (procs.dedup.length - t) _ with
            | none => rw [hfq3] at hmv; simp only [reduceCtorEq] at hmv
            | some w3 =>
              rw [hfq3] at hmv
              simp only [Option.some.injEq] at hmv
              subst w3
              have hdiv3 : (6 * (r / 6) + 3 + 1) / 6 = r / 6 := by omega
              rw [hdiv3]
              by_cases hm : (⟨r / 6, w⟩ : ViewLock V) ∈
                  ((byzQuorumProtocol P V procs leader t).byzantineState
                    F deliver adv x (6 * (r / 6) + 3) h).votedViews
              · simp only [hm, ↓reduceIte]
              · simp only [hm, ↓reduceIte]; exact List.mem_cons_self
        have hcard_sdiff := Finset.le_card_sdiff F (Finset.univ.filter fun j =>
          extractVote (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some val)
        have hcard_le := Finset.card_le_card hsub
        dsimp only
        exact ⟨by omega, by omega⟩
    · rw [byzState_locked_unchanged_of_ne_four leader F deliver adv x r hr4 i] at hlk
      obtain ⟨hlt, hcard⟩ := byzState_locked_witness hprocs hn hF r i hlk
      refine ⟨by omega, le_trans hcard (Finset.card_le_card fun h hh => ?_)⟩
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh ⊢
      exact ⟨hh.1, byzState_votedViews_mono leader F deliver adv x (Nat.le_succ r) h hh.2⟩

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
  have hr5 : r % 6 = 5 := by
    by_contra hne
    rw [byzState_decided_unchanged_of_ne_five leader F deliver adv x r hne i, hnone] at hsome
    simp only [reduceCtorEq] at hsome
  refine ⟨hr5, ?_⟩
  rw [byzQuorum_state_succ] at hsome
  simp only [byzUpdate, hr5] at hsome
  cases hfq : findQuorumVal procs (procs.dedup.length - t)
      (fun j => extractCommit (r / 6) (byzIncoming procs leader t F deliver adv x r i j)) with
  | none =>
    rw [hfq, hnone] at hsome
    simp only [reduceCtorEq] at hsome
  | some w =>
    rw [hfq, hnone] at hsome
    simp only [Option.none_or, Option.some.injEq] at hsome
    subst hsome
    have hiff := findQuorumVal_dedup_sub hprocs (by omega) _ hfq
    have hsub : (Finset.univ.filter fun j =>
        extractCommit (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some w) \ F ⊆
        (Finset.univ \ F).filter fun q =>
          ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x (r + 1) q).locked = some ⟨r / 6, w⟩ := by
      intro q hq
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with ⟨hqc, hqF⟩
      refine ⟨hqF, ?_⟩
      rw [byzState_locked_unchanged_of_ne_four leader F deliver adv x r (by omega) q]
      have hqc' := byzIncoming_honest_deliver leader hqF rfl hqc
      simp only [byzSend, hr5] at hqc'
      have hr4_eq : r = (6 * (r / 6) + 4) + 1 := by omega
      cases hmc : ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x r q).myCommit with
      | none => rw [hmc] at hqc'; simp only [extractCommit, reduceCtorEq] at hqc'
      | some u =>
        rw [hmc] at hqc'
        simp only [extractCommit, ↓reduceIte, Option.some.injEq] at hqc'
        subst hqc'
        rw [hr4_eq, byzQuorum_state_succ] at hmc ⊢
        have hm4 : (6 * (r / 6) + 4) % 6 = 4 := by omega
        have hd4 : (6 * (r / 6) + 4) / 6 = r / 6 := by omega
        simp only [byzUpdate, hm4, hd4] at hmc ⊢
        cases hfq4 : findQuorumVal (V := V) procs (procs.dedup.length - t) _ with
        | none => rw [hfq4] at hmc; simp only [reduceCtorEq] at hmc
        | some u4 =>
          rw [hfq4] at hmc
          simp only [Option.some.injEq] at hmc ⊢
          subst hmc
          congr 1; omega
    have hcard_sdiff := Finset.le_card_sdiff F (Finset.univ.filter fun j =>
      extractCommit (r / 6) (byzIncoming procs leader t F deliver adv x r i j) = some w)
    have hcard_le := Finset.card_le_card hsub
    omega

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
  simp only [byzIncoming, hhF, ↓reduceIte] at hecho
  cases hdel : deliver (6 * v + 3) h p
  · rw [hdel] at hecho
    simp only [Bool.false_eq_true, ↓reduceIte, extractEcho, reduceCtorEq] at hecho
  · rw [hdel] at hecho
    simp only [↓reduceIte, byzSend, show (6 * v + 3) / 6 = v by omega,
      show (6 * v + 3) % 6 = 3 by omega] at hecho
    have hme : ((byzQuorumProtocol P V procs leader t).byzantineState
        F deliver adv x ((6 * v + 2) + 1) h).myEcho = some val := by
      have heq3 : (6 * v + 2) + 1 = 6 * v + 3 := by omega
      rw [heq3]
      cases hm : ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (6 * v + 3) h).myEcho with
      | none => rw [hm] at hecho; simp only [extractEcho, reduceCtorEq] at hecho
      | some w =>
        rw [hm] at hecho
        simp only [extractEcho, ↓reduceIte, Option.some.injEq] at hecho
        rw [hecho]
    rw [byzQuorum_state_succ] at hme
    have hm2 : (6 * v + 2) % 6 = 2 := by omega
    have hd2 : (6 * v + 2) / 6 = v := by omega
    simp only [byzUpdate, hm2, hd2] at hme
    cases hml : byzIncoming procs leader t F deliver adv x (6 * v + 2) h (leader v) with
    | none => rw [hml] at hme; simp only [reduceCtorEq] at hme
    | some msg =>
      rw [hml] at hme
      cases msg with
      | propose v' prop =>
        dsimp only at hme
        split_ifs at hme with hacc
        simp only [Option.some.injEq] at hme
        exact ⟨prop, hme, hacc.2⟩
      | _ => simp only [reduceCtorEq] at hme

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
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · intro r p val hmem
        simp only [Nat.add_zero] at hmem
        have hne : L₀.Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨q₀, hq₀⟩ := hne
        obtain ⟨_, hwit⟩ := byzState_locked_witness leader hprocs hn hF
          (6 * (v₀ + 1)) q₀ (hL₀_lock q₀ hq₀)
        obtain ⟨h₀, hh₀⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit)
        simp only [Finset.mem_filter] at hh₀
        exact votedViews_unique_in_view leader hprocs hn hF hmem hh₀.2
      · intro r p val hmem
        by_contra hne_val
        obtain ⟨_, hq_echo⟩ := votedViews_origin leader hprocs hn r p hmem
        dsimp only at hq_echo
        set v := v₀ + d
        have hprev_lock : ∀ q ∈ L₀, ∃ u_q, v₀ ≤ u_q ∧
            ((byzQuorumProtocol P V procs leader t).byzantineState
              F deliver adv x (6 * v) q).locked = some ⟨u_q, val₀⟩ := by
          intro q hq
          have heq : 6 * v = 6 * (v₀ + (d - 1) + 1) := by omega
          rw [heq]
          exact (ih (d - 1) (by omega)).2 q hq
        obtain ⟨qStar, hqInter, -⟩ := quorum_inter_notMem (F := ∅)
          (S₁ := Finset.univ.filter fun j =>
            extractEcho v (byzIncoming procs leader t F deliver adv x (6 * v + 3) p j) = some val)
          (S₂ := L₀)
          (by simp only [Finset.card_empty]; omega)
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hqInter
        rcases hqInter with ⟨hqE, hqL₀⟩
        have hqF : qStar ∉ F := (Finset.mem_sdiff.1 (hL₀_sub hqL₀)).2
        obtain ⟨u_q, hu_ge, hqlk0⟩ := hprev_lock qStar hqL₀
        have hqlk2 : ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x (6 * v + 2) qStar).locked = some ⟨u_q, val₀⟩ := by
          rw [show 6 * v + 2 = (6 * v + 1) + 1 by omega,
            byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + 1) (by omega),
            byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v) (by omega)]
          exact hqlk0
        obtain ⟨prop, hprop_val, hacc⟩ := honest_echo_accepted leader hqF hqE
        subst hprop_val
        simp only [acceptsProposal, hqlk2] at hacc
        cases hcv : prop.certView with
        | none =>
          rw [hcv] at hacc
          simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true] at hacc
        | some u_cert =>
          rw [hcv] at hacc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
          rcases hacc with ⟨hvc, hcmp⟩
          have hu_le : u_q ≤ u_cert := by
            rcases hcmp with heq | hle
            · exact absurd heq hne_val
            · exact hle
          obtain ⟨hu_lt, h', -, hh'mem⟩ := voterCerts_sound leader hF v qStar hvc
          have hu_lt' : u_cert < v₀ + d := hu_lt
          have hd' : u_cert - v₀ < d := by omega
          have hh'mem' : ⟨v₀ + (u_cert - v₀), prop.val⟩ ∈
              ((byzQuorumProtocol P V procs leader t).byzantineState
                F deliver adv x (6 * v) h').votedViews := by
            convert hh'mem using 2
            omega
          have hval_eq := (ih (u_cert - v₀) hd').1 (6 * v) h' prop.val hh'mem'
          exact hne_val hval_eq
    refine ⟨hv_vote, fun q hq => ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · exact ⟨v₀, le_rfl, hL₀_lock q hq⟩
    · let v := v₀ + d
      have heq_prev : 6 * v = 6 * (v₀ + (d - 1) + 1) := by omega
      obtain ⟨u_prev, hu_prev, hlk_prev⟩ := (ih (d - 1) (by omega)).2 q hq
      rw [← heq_prev] at hlk_prev
      have hlk4 : ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (6 * v + 4) q).locked = some ⟨u_prev, val₀⟩ := by
        rw [show 6 * v + 4 = (6 * v + 3) + 1 by omega,
          byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + 3) (by omega),
          show 6 * v + 3 = (6 * v + 2) + 1 by omega,
          byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + 2) (by omega),
          show 6 * v + 2 = (6 * v + 1) + 1 by omega,
          byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + 1) (by omega),
          byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v) (by omega)]
        exact hlk_prev
      have hlk6 : ((byzQuorumProtocol P V procs leader t).byzantineState
          F deliver adv x (6 * (v + 1)) q).locked =
          ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x ((6 * v + 4) + 1) q).locked := by
        rw [show 6 * (v + 1) = (6 * v + 5) + 1 by omega,
          byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * v + 5) (by omega)]
      rw [show 6 * (v₀ + d + 1) = 6 * (v + 1) by rfl, hlk6]
      have hm4 : (6 * v + 4) % 6 = 4 := by omega
      have hd4 : (6 * v + 4) / 6 = v := by omega
      cases hfq4 : findQuorumVal procs (procs.dedup.length - t)
          (fun j => extractVote v (byzIncoming procs leader t F deliver adv x (6 * v + 4) q j)) with
      | none =>
        rw [byzQuorum_state_succ]
        simp only [byzUpdate, hm4, hd4, hfq4]
        exact ⟨u_prev, hu_prev, hlk4⟩
      | some w =>
        have hw_lk : ((byzQuorumProtocol P V procs leader t).byzantineState
            F deliver adv x ((6 * v + 4) + 1) q).locked = some ⟨v, w⟩ := by
          rw [byzQuorum_state_succ]
          simp only [byzUpdate, hm4, hd4, hfq4]
        obtain ⟨_, hwit⟩ := byzState_locked_witness leader hprocs hn hF ((6 * v + 4) + 1) q hw_lk
        obtain ⟨h, hh⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit)
        simp only [Finset.mem_filter] at hh
        have hw_eq : w = val₀ := hv_vote ((6 * v + 4) + 1) h w hh.2
        exact ⟨v, by omega, by rw [hw_lk, hw_eq]⟩

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
      have hw : (byzQuorumProtocol P V procs leader t).byzantineDecision
          F deliver adv x (r + 1) i = some w :=
        byzQuorum_irrevocable leader F deliver adv x (Nat.le_succ r) i w hprev
      have heq : w = val := Option.some.inj (hw.symm.trans h)
      subst heq
      obtain ⟨m, hm_lt, hmn, hms⟩ := first_decision_round r i hprev
      exact ⟨m, Nat.lt_succ_of_lt hm_lt, hmn, hms⟩

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
  let u₁ := m₁ / 6
  let u₂ := m₂ / 6
  have hm₁_eq : m₁ + 1 = 6 * (u₁ + 1) := by omega
  have hm₂_eq : m₂ + 1 = 6 * (u₂ + 1) := by omega
  rw [hm₁_eq] at hL₁
  rw [hm₂_eq] at hL₂
  obtain ⟨q₁, hq₁⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL₁)
  obtain ⟨q₂, hq₂⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL₂)
  simp only [Finset.mem_filter] at hq₁ hq₂
  obtain ⟨_, hwit₁⟩ := byzState_locked_witness leader hprocs hn hF (6 * (u₁ + 1)) q₁ hq₁.2
  obtain ⟨_, hwit₂⟩ := byzState_locked_witness leader hprocs hn hF (6 * (u₂ + 1)) q₂ hq₂.2
  obtain ⟨h₁', hh₁'⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit₁)
  obtain ⟨h₂', hh₂'⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit₂)
  simp only [Finset.mem_filter] at hh₁' hh₂'
  rcases le_total u₁ u₂ with hle | hle
  · have hpres := (byzQuorum_lock_preservation leader hprocs hn hF
      (Finset.filter_subset _ _) hL₁
      (fun q hq => (Finset.mem_filter.1 hq).2) (u₂ - u₁)).1
      (6 * (u₂ + 1)) h₂' v₂ (by rw [Nat.add_sub_of_le hle]; exact hh₂'.2)
    exact hpres.symm
  · have hpres := (byzQuorum_lock_preservation leader hprocs hn hF
      (Finset.filter_subset _ _) hL₂
      (fun q hq => (Finset.mem_filter.1 hq).2) (u₁ - u₂)).1
      (6 * (u₁ + 1)) h₁' v₁ (by rw [Nat.add_sub_of_le hle]; exact hh₁'.2)
    exact hpres

/-- When all correct processes start with `val₀` (`∀ h ∉ F, x h = val₀`) and `F.card ≤ t`, every
process's Subround-0 `properReport` has `allProper = false` and `freqVals ⊆ {val₀}`. -/
private theorem properReport_unanimous {F : Finset P} {deliver : ℕ → P → P → Bool}
    {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V} {val₀ : V}
    (hF : F.card ≤ t) (hx : ∀ h ∉ F, x h = val₀) (v : ℕ) (i : P) :
    let rep := ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * v + 1) i).properReport
    rep.allProper = false ∧ ∀ w ∈ rep.freqVals, w = val₀ := by
  rw [show 6 * v + 1 = (6 * v) + 1 by rfl, byzQuorum_state_succ]
  simp only [byzUpdate, show (6 * v) % 6 = 0 by omega, show (6 * v) / 6 = v by omega,
    computeProperReport]
  let initFrom := fun j =>
    extractRawInit (byzIncoming procs leader t F deliver adv x (6 * v) i j)
  have hhonest_val : ∀ h ∉ F, ∀ w, initFrom h = some w → w = val₀ := by
    intro h hhF w hw
    simp only [initFrom, byzIncoming, hhF, ↓reduceIte] at hw
    cases hdel : deliver (6 * v) h i
    · rw [hdel] at hw
      simp only [Bool.false_eq_true, ↓reduceIte, extractRawInit, reduceCtorEq] at hw
    · rw [hdel] at hw
      simp only [↓reduceIte, byzSend, show (6 * v) % 6 = 0 by omega, extractRawInit,
        byzState_input_eq, Option.some.injEq] at hw
      rw [← hw, hx h hhF]
  constructor
  · rw [decide_eq_false_iff_not]
    rintro ⟨hrep_len, hall⟩
    change 2 * t + 1 ≤ (procs.dedup.filter fun j => (initFrom j).isSome).length at hrep_len
    have hnd_rep : (procs.dedup.filter fun j => (initFrom j).isSome).Nodup :=
      List.Nodup.filter _ (List.nodup_dedup procs)
    rw [← List.toFinset_card_of_nodup hnd_rep] at hrep_len
    obtain ⟨h₀, hh₀, hh₀F⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show F.card < (procs.dedup.filter fun j => (initFrom j).isSome).toFinset.card by omega)
    rw [List.mem_toFinset] at hh₀
    have hh₀_some : (initFrom h₀).isSome = true := (List.mem_filter.1 hh₀).2
    obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 hh₀_some
    have hw₀_eq : w₀ = val₀ := hhonest_val h₀ hh₀F w₀ hw₀
    subst hw₀_eq
    have hcnt := hall h₀ hh₀
    have hnd : ((procs.dedup.filter fun j => (initFrom j).isSome).filter
        fun k => decide (initFrom k ≠ initFrom h₀)).Nodup :=
      List.Nodup.filter _ hnd_rep
    rw [← List.toFinset_card_of_nodup hnd] at hcnt
    have hsub : ((procs.dedup.filter fun j => (initFrom j).isSome).filter
        fun k => decide (initFrom k ≠ initFrom h₀)).toFinset ⊆ F := by
      intro k hk
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hk
      by_contra hkF
      obtain ⟨wk, hwk⟩ := Option.isSome_iff_exists.1 hk.1.2
      rw [hhonest_val k hkF wk hwk] at hwk
      exact hk.2 (hwk.trans hw₀.symm)
    have hle := Finset.card_le_card hsub
    omega
  · intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    rcases hw with ⟨_, hcnt⟩
    change t + 1 ≤ (procs.dedup.filter fun j => decide (initFrom j = some w)).length at hcnt
    have hnd_w : (procs.dedup.filter fun j => decide (initFrom j = some w)).Nodup :=
      List.Nodup.filter _ (List.nodup_dedup procs)
    rw [← List.toFinset_card_of_nodup hnd_w] at hcnt
    obtain ⟨h, hh, hhF⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hF hcnt)
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hh
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
        rw [hcv] at hacc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
        have hcnt := hacc.2
        rw [show 6 * u + 2 = (6 * u + 1) + 1 by omega, byzQuorum_state_succ] at hcnt
        have hm1 : (6 * u + 1) % 6 = 1 := by omega
        simp only [byzUpdate, hm1, properSupportCount, filterMap_fst_filter_length] at hcnt
        have hnd : (procs.dedup.filter fun j =>
            match extractCertStatus
                (byzIncoming procs leader t F deliver adv x (6 * u + 1) h j) with
            | some (rep, _) => rep.allProper || decide (prop.val ∈ rep.freqVals)
            | none => false).Nodup :=
          List.Nodup.filter _ (List.nodup_dedup procs)
        rw [← List.toFinset_card_of_nodup hnd] at hcnt
        obtain ⟨r', hr', hr'F⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (lt_of_le_of_lt hF hcnt)
        simp only [List.mem_toFinset, List.mem_filter, byzIncoming, hr'F, ↓reduceIte] at hr'
        rcases hr' with ⟨_, hr'⟩
        cases hdel' : deliver (6 * u + 1) r' h
        · rw [hdel'] at hr'
          simp only [Bool.false_eq_true, ↓reduceIte, extractCertStatus, Bool.false_eq_true] at hr'
        · rw [hdel'] at hr'
          simp only [↓reduceIte, byzSend, hm1, extractCertStatus, Bool.or_eq_true,
            decide_eq_true_eq] at hr'
          obtain ⟨hap, hfv⟩ := properReport_unanimous leader hF hx u r'
          rcases hr' with hap_true | hmem_fv
          · rw [hap] at hap_true; exact Bool.noConfusion hap_true
          · exact hfv prop.val hmem_fv
      | some u_cert =>
        rw [hcv] at hacc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
        obtain ⟨hu_lt, h', -, hh'mem⟩ := voterCerts_sound leader hF u h hacc.1
        exact ih u_cert hu_lt (6 * u) h' prop.val hh'mem
  intro r i w hdec
  obtain ⟨m, -, hmn, hms⟩ := first_decision_round leader r i hdec
  obtain ⟨_, hL⟩ := decision_step_locks leader hprocs hn hF hmn hms
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hL)
  simp only [Finset.mem_filter] at hq
  obtain ⟨_, hwit⟩ := byzState_locked_witness leader hprocs hn hF (m + 1) q hq.2
  obtain ⟨h, hh⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit)
  simp only [Finset.mem_filter] at hh
  exact hvote_valid (m / 6) (m + 1) h w hh.2

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
    have ih := omissionState_input_eq deliver x r i
    rw [omissionQuorum_state_succ]
    simp only [omissionUpdate]
    have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · simp only [h0]; exact ih
    · simp only [h1]
      cases hm : omissionIncoming procs leader t deliver x r i (leader (r / 3)) with
      | none => exact ih
      | some msg =>
        cases msg with
        | propose v' prop =>
          by_cases hok : acceptsOmissionProposal (r / 3) v'
            ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i) prop <;>
            simp [hok, ih]
        | _ => exact ih
    · simp only [h2]; cases findQuorumVal (V := V) procs _ _ <;> exact ih

private theorem omission_decided_unchanged_of_ne_two (deliver : ℕ → P → P → Bool) (x : P → V)
    (r : ℕ) (h : r % 3 ≠ 2) (i : P) :
    ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (r + 1) i).decided =
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).decided := by
  rw [omissionQuorum_state_succ]
  simp only [omissionUpdate]
  have hmod : r % 3 = 0 ∨ r % 3 = 1 := by omega
  rcases hmod with h0 | h1
  · simp only [h0]
  · simp only [h1]
    cases omissionIncoming procs leader t deliver x r i (leader (r / 3)) with
    | none => rfl
    | some msg =>
      cases msg with
      | propose v' prop =>
        by_cases hok : acceptsOmissionProposal (r / 3) v'
          ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i) prop <;>
          simp [hok]
      | _ => rfl

/-- Decisions of `omissionQuorumProtocol` are write-once across all rounds. -/
theorem omission_irrevocable (deliver : ℕ → P → P → Bool) (x : P → V)
    {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) (i : P) (val : V)
    (hdec : (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₁ i =
      some val) :
    (omissionQuorumProtocol P V procs leader t).omissionDecision deliver x r₂ i = some val := by
  induction hr with
  | refl => exact hdec
  | @step m _ ih =>
    change ((omissionQuorumProtocol P V procs leader t).omissionState deliver x m i).decided =
      some val at ih
    change ((omissionQuorumProtocol P V procs leader t).omissionState
      deliver x (m + 1) i).decided = some val
    by_cases hm2 : m % 3 = 2
    · rw [omissionQuorum_state_succ]
      simp only [omissionUpdate, hm2]
      cases findQuorumVal (V := V) procs _ _ with
      | none => exact ih
      | some w => simp only [ih, Option.some_or]
    · rw [omission_decided_unchanged_of_ne_two leader deliver x m hm2 i]
      exact ih

theorem omission_locked_unchanged_of_ne_one (deliver : ℕ → P → P → Bool) (x : P → V)
    (r : ℕ) (h : r % 3 ≠ 1) (i : P) :
    ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (r + 1) i).locked =
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i).locked := by
  rw [omissionQuorum_state_succ]
  simp only [omissionUpdate]
  have hmod : r % 3 = 0 ∨ r % 3 = 2 := by omega
  rcases hmod with h0 | h2
  · simp only [h0]
  · simp only [h2]; cases findQuorumVal (V := V) procs _ _ <;> rfl

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
    by_cases hr1 : r % 3 = 1
    · rw [omissionQuorum_state_succ] at hlk
      simp only [omissionUpdate, hr1] at hlk
      cases hdel : deliver r (leader (r / 3)) i
      · simp only [omissionIncoming, hdel, Bool.false_eq_true, ↓reduceIte] at hlk
        obtain ⟨hlt, hprop⟩ := omissionState_locked_origin deliver x r i hlk
        exact ⟨by omega, hprop⟩
      · simp only [omissionIncoming, hdel, ↓reduceIte, omissionSend, hr1] at hlk
        cases hlp : ((omissionQuorumProtocol P V procs leader t).omissionState
            deliver x r (leader (r / 3))).leaderProposal with
        | none =>
          rw [hlp] at hlk
          obtain ⟨hlt, hprop⟩ := omissionState_locked_origin deliver x r i hlk
          exact ⟨by omega, hprop⟩
        | some prop =>
          rw [hlp] at hlk
          by_cases hok : acceptsOmissionProposal (r / 3) (r / 3)
              ((omissionQuorumProtocol P V procs leader t).omissionState deliver x r i) prop
          · simp only [hok, ↓reduceIte, Option.some.injEq] at hlk
            subst hlk
            dsimp only
            have hr_eq : 3 * (r / 3) + 1 = r := by omega
            exact ⟨by omega, prop.certView, by rw [hr_eq]; exact hlp⟩
          · simp only [hok, Bool.false_eq_true, ↓reduceIte] at hlk
            obtain ⟨hlt, hprop⟩ := omissionState_locked_origin deliver x r i hlk
            exact ⟨by omega, hprop⟩
    · rw [omission_locked_unchanged_of_ne_one leader deliver x r hr1 i] at hlk
      obtain ⟨hlt, hprop⟩ := omissionState_locked_origin deliver x r i hlk
      exact ⟨by omega, hprop⟩

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
      have hw := omission_irrevocable leader deliver x (Nat.le_succ r) i w hprev
      have heq : w = val := Option.some.inj (hw.symm.trans h)
      subst heq
      obtain ⟨m, hm_lt, hmn, hms⟩ := omission_first_decision deliver x r i hprev
      exact ⟨m, Nat.lt_succ_of_lt hm_lt, hmn, hms⟩

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
  have hr2 : r % 3 = 2 := by
    by_contra hne
    rw [omission_decided_unchanged_of_ne_two leader deliver x r hne i, hnone] at hsome
    simp only [reduceCtorEq] at hsome
  refine ⟨hr2, ?_⟩
  rw [omissionQuorum_state_succ] at hsome
  simp only [omissionUpdate, hr2] at hsome
  cases hfq : findQuorumVal procs (procs.dedup.length - t)
      (fun j => extractAck (r / 3) (omissionIncoming procs leader t deliver x r i j)) with
  | none =>
    rw [hfq, hnone] at hsome
    simp only [reduceCtorEq] at hsome
  | some w =>
    rw [hfq, hnone] at hsome
    simp only [Option.none_or, Option.some.injEq] at hsome
    subst hsome
    refine le_trans (findQuorumVal_dedup_sub hprocs (by omega) _ hfq)
      (Finset.card_le_card fun q hq => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [omission_locked_unchanged_of_ne_one leader deliver x r (by omega) q]
    cases hdel : deliver r q i
    · simp only [omissionIncoming, hdel, Bool.false_eq_true, ↓reduceIte, extractAck,
        reduceCtorEq] at hq
    · simp only [omissionIncoming, hdel, ↓reduceIte, omissionSend, hr2] at hq
      have hr1_eq : r = (3 * (r / 3) + 1) + 1 := by omega
      cases hma : ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x r q).myAck with
      | none => rw [hma] at hq; simp only [extractAck, reduceCtorEq] at hq
      | some u =>
        rw [hma] at hq
        simp only [extractAck, ↓reduceIte, Option.some.injEq] at hq
        subst hq
        rw [hr1_eq, omissionQuorum_state_succ] at hma ⊢
        have hm1 : (3 * (r / 3) + 1) % 3 = 1 := by omega
        have hd1 : (3 * (r / 3) + 1) / 3 = r / 3 := by omega
        simp only [omissionUpdate, hm1, hd1] at hma ⊢
        cases hinc : omissionIncoming procs leader t deliver x
            (3 * (r / 3) + 1) q (leader (r / 3)) with
        | none => rw [hinc] at hma; simp only [reduceCtorEq] at hma
        | some msg =>
          rw [hinc] at hma
          cases msg with
          | propose v' prop =>
            by_cases hok : acceptsOmissionProposal (r / 3) v'
              ((omissionQuorumProtocol P V procs leader t).omissionState
                deliver x (3 * (r / 3) + 1) q) prop
            · simp only [hok, ↓reduceIte, Option.some.injEq] at hma ⊢
              rw [hma]
              congr 1; omega
            · simp only [hok, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hma
          | _ => simp only [reduceCtorEq] at hma

private theorem extractStatusLock_incoming_locked (deliver : ℕ → P → P → Bool) (x : P → V)
    {v : ℕ} {jb : P} {best : ViewLock V}
    (hjb : extractStatusLock (omissionIncoming procs leader t deliver x (3 * v) (leader v) jb) =
      some best) :
    best.view < v ∧
      ((omissionQuorumProtocol P V procs leader t).omissionState deliver x (3 * v) jb).locked =
        some best := by
  cases hdel : deliver (3 * v) jb (leader v)
  · simp only [omissionIncoming, hdel, Bool.false_eq_true, ↓reduceIte, extractStatusLock,
      reduceCtorEq] at hjb
  · simp only [omissionIncoming, hdel, ↓reduceIte, omissionSend,
      show (3 * v) % 3 = 0 by omega] at hjb
    cases hjblk : ((omissionQuorumProtocol P V procs leader t).omissionState
        deliver x (3 * v) jb).locked with
    | none => rw [hjblk] at hjb; simp only [extractStatusLock, reduceCtorEq] at hjb
    | some lk_b =>
      rw [hjblk] at hjb
      simp only [extractStatusLock, Option.some.injEq] at hjb
      subst hjb
      obtain ⟨hlt_b, -⟩ := omissionState_locked_origin leader deliver x (3 * v) jb hjblk
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
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · intro r p val hlk
        simp only [Nat.add_zero] at hlk
        obtain ⟨q₀, hq₀⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hQ₀_card)
        obtain ⟨_, cv₁, hp₁⟩ := omissionState_locked_origin leader deliver x r p hlk
        obtain ⟨_, cv₂, hp₂⟩ := omissionState_locked_origin leader deliver x
          (3 * (v₀ + 1)) q₀ (hQ₀_lock q₀ hq₀)
        have heq := Option.some.inj (hp₁.symm.trans hp₂)
        exact congrArg Proposal.val heq
      · intro r p val hlk
        obtain ⟨_, cv, hlp⟩ := omissionState_locked_origin leader deliver x r p hlk
        dsimp only at hlp
        set v := v₀ + d
        have hprev_Q : ∀ q ∈ Q₀, ∃ u_q, v₀ ≤ u_q ∧
            ((omissionQuorumProtocol P V procs leader t).omissionState
              deliver x (3 * v) q).locked = some ⟨u_q, val₀⟩ := by
          intro q hq
          have heq : 3 * v = 3 * (v₀ + (d - 1) + 1) := by omega
          rw [heq]
          exact (ih (d - 1) (by omega)).2 q hq
        rw [show 3 * v + 1 = (3 * v) + 1 by rfl, omissionQuorum_state_succ] at hlp
        simp only [omissionUpdate, show (3 * v) % 3 = 0 by omega] at hlp
        split_ifs at hlp with hcnt
        have hlen := dedup_length_eq_card hprocs
        rw [hlen, length_filter_dedup_eq_card hprocs] at hcnt
        obtain ⟨qStar, hqInter, -⟩ := quorum_inter_notMem (F := ∅)
          (S₁ := Finset.univ.filter fun j =>
            isOmissionStatus (omissionIncoming procs leader t deliver x (3 * v) (leader v) j) =
              true)
          (S₂ := Q₀)
          (by simp only [Finset.card_empty]; omega)
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hqInter
        rcases hqInter with ⟨hqS, hqQ₀⟩
        obtain ⟨u_q, hu_ge, hqlk⟩ := hprev_Q qStar hqQ₀
        cases hdel : deliver (3 * v) qStar (leader v)
        · simp only [omissionIncoming, hdel, Bool.false_eq_true, ↓reduceIte,
            isOmissionStatus, Bool.false_eq_true] at hqS
        · let locksList := procs.dedup.filterMap fun j =>
            extractStatusLock (omissionIncoming procs leader t deliver x (3 * v) (leader v) j)
          have hmem_locks : (⟨u_q, val₀⟩ : ViewLock V) ∈ locksList := by
            rw [List.mem_filterMap]
            refine ⟨qStar, List.mem_dedup.2 (hprocs qStar), ?_⟩
            simp only [omissionIncoming, hdel, ↓reduceIte, omissionSend,
              show (3 * v) % 3 = 0 by omega, hqlk, extractStatusLock]
          cases hpm : pickMaxLock locksList with
          | none =>
            have hemp : locksList = [] := pickMaxLock_eq_none_iff.1 hpm
            rw [hemp] at hmem_locks
            exact absurd hmem_locks List.not_mem_nil
          | some best =>
            have hpm' : pickMaxLock (procs.dedup.filterMap fun j =>
                extractStatusLock
                  (omissionIncoming procs leader t deliver x (3 * v) (leader v) j)) =
                some best := hpm
            rw [hpm'] at hlp
            simp only [Option.some.injEq, Proposal.mk.injEq] at hlp
            have hbest_mem := pickMaxLock_mem hpm
            have hbest_ge : v₀ ≤ best.view := le_trans hu_ge (pickMaxLock_le hpm _ hmem_locks)
            obtain ⟨jb, -, hjb⟩ := List.mem_filterMap.1 hbest_mem
            obtain ⟨hlt_b, hjblk⟩ := extractStatusLock_incoming_locked leader deliver x hjb
            have hlt_b' : best.view < v₀ + d := hlt_b
            have hd' : best.view - v₀ < d := by omega
            have hview_eq : v₀ + (best.view - v₀) = best.view := by omega
            have hval_b := (ih (best.view - v₀) hd').1 (3 * v) jb best.val
              (by rw [hview_eq]; exact hjblk)
            exact hlp.1.symm.trans hval_b
    refine ⟨hv_lock, fun q hq => ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · exact ⟨v₀, le_rfl, hQ₀_lock q hq⟩
    · set v := v₀ + d
      have heq_prev : 3 * v = 3 * (v₀ + (d - 1) + 1) := by omega
      obtain ⟨u_prev, hu_prev, hlk_prev⟩ := (ih (d - 1) (by omega)).2 q hq
      rw [← heq_prev] at hlk_prev
      have hlk1 : ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x (3 * v + 1) q).locked = some ⟨u_prev, val₀⟩ := by
        rw [omission_locked_unchanged_of_ne_one leader deliver x (3 * v) (by omega)]
        exact hlk_prev
      have hlk3 : ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x (3 * (v + 1)) q).locked =
          ((omissionQuorumProtocol P V procs leader t).omissionState
            deliver x ((3 * v + 1) + 1) q).locked := by
        rw [show 3 * (v + 1) = (3 * v + 2) + 1 by omega,
          omission_locked_unchanged_of_ne_one leader deliver x (3 * v + 2) (by omega)]
      rw [show 3 * (v₀ + d + 1) = 3 * (v + 1) by rfl, hlk3]
      have hm1 : (3 * v + 1) % 3 = 1 := by omega
      have hd1 : (3 * v + 1) / 3 = v := by omega
      have hcases : ((omissionQuorumProtocol P V procs leader t).omissionState
          deliver x ((3 * v + 1) + 1) q).locked = some ⟨u_prev, val₀⟩ ∨
          ∃ w, ((omissionQuorumProtocol P V procs leader t).omissionState
            deliver x ((3 * v + 1) + 1) q).locked = some ⟨v, w⟩ := by
        rw [omissionQuorum_state_succ]
        simp only [omissionUpdate, hm1, hd1]
        cases hinc : omissionIncoming procs leader t deliver x (3 * v + 1) q (leader v) with
        | none => exact Or.inl hlk1
        | some msg =>
          cases msg with
          | propose v' prop =>
            by_cases hok : acceptsOmissionProposal v v'
                ((omissionQuorumProtocol P V procs leader t).omissionState
                  deliver x (3 * v + 1) q) prop
            · simp only [hok, ↓reduceIte]; exact Or.inr ⟨prop.val, rfl⟩
            · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact Or.inl hlk1
          | _ => exact Or.inl hlk1
      rcases hcases with hkeep | ⟨w, hupd⟩
      · exact ⟨u_prev, hu_prev, hkeep⟩
      · have hw_eq := hv_lock ((3 * v + 1) + 1) q w hupd
        subst hw_eq
        exact ⟨v, by omega, hupd⟩

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
  have hm_eq : m + 1 = 3 * (u + 1) := by omega
  rw [hm_eq] at hQ
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
      rw [show 3 * u + 1 = (3 * u) + 1 by rfl, omissionQuorum_state_succ] at hlp
      simp only [omissionUpdate, show (3 * u) % 3 = 0 by omega] at hlp
      split_ifs at hlp with hcnt
      cases hpm : pickMaxLock _ with
      | none =>
        rw [hpm] at hlp
        simp only [Option.some.injEq, Proposal.mk.injEq] at hlp
        rw [← hlp.1, omissionState_input_eq, hx]
      | some best =>
        rw [hpm] at hlp
        simp only [Option.some.injEq, Proposal.mk.injEq] at hlp
        have hmem := pickMaxLock_mem hpm
        obtain ⟨jb, -, hjb⟩ := List.mem_filterMap.1 hmem
        obtain ⟨hlt_b, hjblk⟩ := extractStatusLock_incoming_locked leader deliver x hjb
        exact hlp.1.symm.trans (ih best.view hlt_b (3 * u) jb best.val hjblk)
  intro r i w hdec
  obtain ⟨m, -, hmn, hms⟩ := omission_first_decision leader deliver x r i hdec
  obtain ⟨_, hQ⟩ := omission_decision_step_quorum leader hprocs hn deliver x hmn hms
  obtain ⟨q, hq⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hQ)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  exact hlock_val (m / 3) (m + 1) q w hq

end OmissionSafety

end Cslib.Distributed.PartialSynchrony
