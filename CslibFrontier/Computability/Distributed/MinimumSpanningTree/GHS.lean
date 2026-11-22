/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MinimumSpanningTree
public import Cslib.Foundations.Semantics.LTS.Basic
import Mathlib.Data.Nat.Log

/-!
# Event-Driven Fragment-Phase Gallager–Humblet–Spira (GHS) Distributed MST Protocol

This module formalizes an event-driven fragment-phase execution and seven-type message accounting
model (`fragLTS`) as a milestone step toward `#7508`, after [GallagerHumbletSpira1983]
(Sections 2–4 and Appendix, pp. 68–77).

## Model scope and relationship to [GallagerHumbletSpira1983]

In [GallagerHumbletSpira1983], nodes communicate asynchronously over reliable FIFO links using
local state variables (`SN`, `SE(j)`, `FN`, `LN`, `best-edge`, `best-wt`, `test-edge`, `in-branch`,
`find-count`) and per-node incoming message queues (Appendix rules (1)–(12), pp. 75–77), where
adjacent endpoints may temporarily hold asymmetric `SE(j)` edge states and re-queue premature
`Connect`, `Test`, and `Report` messages.

Here `FragState`, `FragAction`, `fragStep?`, and `fragLTS` model the protocol at the event-driven
fragment-phase level while retaining the exact level/phase synchronization guards and seven-message
breakdown of Sections 3–4:

* edges of `G` are classified into `EdgeState.basic`, `EdgeState.branch` (`s.branchEdges`), and
  `EdgeState.rejected` (`s.rejectedEdges`);
* fragments `(verts, level, core, phase)` progress through `FragPhase.sleeping` (initial level-`0`
  singletons), `FragPhase.searching` (`Find`), `FragPhase.found e` (`Found`, waiting to combine
  along minimum-weight outgoing edge `e`), and `FragPhase.halted`;
* `FragAction.rejectChord` rejects an internal `Basic` chord of a searching fragment either by
  `Test` + `Reject` (`1 + 1` messages) or simultaneous dual `Test` (`2` messages, §3, p. 71);
* `FragAction.completeSearch` enforces the GHS `Test`-delay rule (`allNodeMOEsAccepted`, §3, p. 71
  and Appendix rule (6), p. 76): a fragment at level `L` completes its `Test`/`Accept`/`Report`/
  `Change-root`/`Connect` sweep only when every vertex's minimum-weight outgoing probe targets a
  fragment of level at least `L`;
* `FragAction.absorb` (`F₁.level < F₂.level` into either a `searching` or `found` recipient `F₂`,
  §3, p. 72) and `FragAction.merge` (`F₁.level = F₂.level = L` along a shared mutual MOE `e`,
  forming core `some e` at level `L + 1`, §3, p. 72) broadcast `Initiate` messages across the newly
  joined vertices;
* `FragAction.haltSearch` completes the final `Report(∞)` sweep once a single fragment spans `V`
  and all internal chords have been rejected.

Refining the Appendix per-node asynchronous FIFO message-queue state machine onto `fragLTS`, as well
as the nondistinct-weight `Connect`-cancellation modification (§3, p. 73) and synchronous-awakening
`5 N log₂ N` time bound (§5, p. 74), remains open in `#7508`.

## Main definitions

* `Cslib.Distributed.MinimumSpanningTree.EdgeState`: GHS edge classification (`basic`, `branch`,
  `rejected`).
* `Cslib.Distributed.MinimumSpanningTree.FragPhase`: fragment protocol phase (`sleeping`,
  `searching`, `found`, `halted`).
* `Cslib.Distributed.MinimumSpanningTree.Fragment`: fragment record `(verts, level, core, phase)`.
* `Cslib.Distributed.MinimumSpanningTree.MsgCount`,
  `Cslib.Distributed.MinimumSpanningTree.MsgCount.total`: per-type and total message counters for
  `connect`, `initiate`, `test`, `accept`, `reject`, `report`, and `changeRoot`.
* `Cslib.Distributed.MinimumSpanningTree.FragState`,
  `Cslib.Distributed.MinimumSpanningTree.initFragState`: global fragment-phase configuration and
  initial all-sleeping singleton state.
* `Cslib.Distributed.MinimumSpanningTree.FragAction`,
  `Cslib.Distributed.MinimumSpanningTree.FragAction.isCombine`,
  `Cslib.Distributed.MinimumSpanningTree.fragStep?`,
  `Cslib.Distributed.MinimumSpanningTree.runFragTrace?`,
  `Cslib.Distributed.MinimumSpanningTree.fragLTS`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable`: executable transition function,
  deterministic `Cslib.LTS`, and reachability predicate from `initFragState`.

## Main results

* `Cslib.Distributed.MinimumSpanningTree.FragReachable.branchGraph_le_of_isMST`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.branchGraph_isAcyclic`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.fragment_induce_isTree`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.rejected_internal_chord`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.rejected_notMem_isMST`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.rejected_not_isMOE`: MST-subtree,
  per-fragment spanning-tree, and internal-chord rejection invariants.
* `Cslib.Distributed.MinimumSpanningTree.FragReachable.two_pow_level_le_card`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.level_le_log_card`: exponential fragment
  size `2 ^ F.level ≤ F.verts.card` and logarithmic level bound
  `F.level ≤ Nat.log 2 (Fintype.card V)` (step toward `#7508`, after §3, p. 72).
* `Cslib.Distributed.MinimumSpanningTree.FragReachable.exists_absorb_or_merge_of_minLevel_found`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.exists_step_of_not_halted`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.isTerminal_iff_halted`: deadlock-freedom via
  minimum-level smallest-MOE progress (step toward `#7508`, after §3, pp. 72–73).
* `Cslib.Distributed.MinimumSpanningTree.FragReachable.halted_branchGraph_isMST`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.exists_mTr_halted`,
  `Cslib.Distributed.MinimumSpanningTree.fragLTS_combineSteps_le`,
  `Cslib.Distributed.MinimumSpanningTree.fragLTS_completeTrace_combineSteps_eq`,
  `Cslib.Distributed.MinimumSpanningTree.FragReachable.msgs_total_le`: termination of every maximal
  fragment-phase execution at the exact unique MST in `|V| - 1` combine steps with total messages at
  most `5 * Fintype.card V * Nat.log 2 (Fintype.card V) + 2 * G.edgeFinset.card`
  (step toward `#7508`, after §4, p. 73).

## References

* [R. G. Gallager, P. A. Humblet, and P. M. Spira, *A Distributed Algorithm for Minimum-Weight
  Spanning Trees*][GallagerHumbletSpira1983], Sections 2–4 and Appendix (pp. 68–77).
-/

public section

namespace Cslib.Distributed.MinimumSpanningTree

open SimpleGraph

/-! ### Edge states, fragments, and seven-type message accounting -/

/-- Classification of an undirected edge in the GHS algorithm ([GallagerHumbletSpira1983], §3,
pp. 70–71): `basic` (undecided), `branch` (selected MST tree edge), or `rejected` (non-tree chord
inside a single fragment). -/
inductive EdgeState where
  | basic
  | branch
  | rejected
  deriving @[expose] DecidableEq, Repr

/-- Protocol phase of a fragment in the event-driven fragment-merging GHS model (corresponding to
`Sleeping`, `Find`, `Found` waiting on `Connect(L)`, and halted termination in
[GallagerHumbletSpira1983], §3 & Appendix, pp. 69–77). -/
inductive FragPhase (V : Type*) where
  | sleeping
  | searching
  | found (moe : Sym2 V)
  | halted
  deriving @[expose] DecidableEq

/-- A fragment `(verts, level, core, phase)` in the event-driven GHS protocol
([GallagerHumbletSpira1983], §§2–3, pp. 68–72). -/
structure Fragment (V : Type*) where
  /-- Vertex set of the fragment. -/
  verts : Finset V
  /-- Nonnegative GHS level `L` (`0` for initial singleton fragments). -/
  level : ℕ
  /-- Core edge `some e` for `level ≥ 1` (`none` at `level = 0`), whose weight identifies the
  fragment (`FN` in [GallagerHumbletSpira1983], §3, p. 70). -/
  core : Option (Sym2 V)
  /-- Current protocol phase of the fragment. -/
  phase : FragPhase V
  deriving @[expose] DecidableEq

/-- Cumulative counts of the seven message types of [GallagerHumbletSpira1983] (§§3–4,
pp. 69–73). -/
structure MsgCount where
  /-- `Connect(L)` messages sent across minimum-weight outgoing edges. -/
  connect : ℕ := 0
  /-- `Initiate(L, F, S)` messages broadcast outward along fragment branches. -/
  initiate : ℕ := 0
  /-- `Test(L, F)` probes sent across `Basic` edges. -/
  test : ℕ := 0
  /-- `Accept` replies certifying outgoing `Basic` edges. -/
  accept : ℕ := 0
  /-- `Reject` replies on internal chord `Basic` edges. -/
  reject : ℕ := 0
  /-- `Report(W)` convergecast messages sent inward along fragment branches. -/
  report : ℕ := 0
  /-- `Change-root` (`Change-core`) messages sent from the core toward the MOE endpoint. -/
  changeRoot : ℕ := 0
  deriving @[expose] DecidableEq, Repr

/-- Total messages exchanged across all seven GHS message types. -/
@[expose] def MsgCount.total (m : MsgCount) : ℕ :=
  m.connect + m.initiate + m.test + m.accept + m.reject + m.report + m.changeRoot

/-- Global configuration of the event-driven fragment-phase GHS protocol on vertex type `V`. -/
structure FragState (V : Type*) where
  /-- Active partition of `V` into fragments. -/
  fragments : Finset (Fragment V)
  /-- Undirected edges currently classified as `Branch`. -/
  branchEdges : Finset (Sym2 V)
  /-- Undirected edges currently classified as `Rejected`. -/
  rejectedEdges : Finset (Sym2 V)
  /-- Cumulative per-type message counters. -/
  msgs : MsgCount
  deriving @[expose] DecidableEq

/-- Edge classification of `e` in `s : FragState V`. -/
@[expose] def FragState.edgeState {V : Type*} [DecidableEq V] (s : FragState V)
    (e : Sym2 V) : EdgeState :=
  if e ∈ s.branchEdges then .branch
  else if e ∈ s.rejectedEdges then .rejected
  else .basic

/-- Spanning subgraph of `V` formed by `s.branchEdges`. -/
@[expose] def FragState.branchGraph {V : Type*} (s : FragState V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (s.branchEdges : Set (Sym2 V))

instance instDecidableRelBranchGraphAdj {V : Type*} [DecidableEq V] (s : FragState V) :
    DecidableRel s.branchGraph.Adj := by
  unfold FragState.branchGraph
  infer_instance

/-- A configuration `s` has halted once there is a halted fragment in `s.fragments` (which by the
reachable invariant implies `s.fragments` is a single spanning fragment on `Finset.univ`). -/
@[expose] def FragState.Halted {V : Type*} (s : FragState V) : Prop :=
  ∃ F ∈ s.fragments, F.phase = .halted

instance instDecidableFragStateHalted {V : Type*} [DecidableEq V] (s : FragState V) :
    Decidable s.Halted := by
  unfold FragState.Halted
  infer_instance

/-- Initial quiescent configuration ([GallagerHumbletSpira1983], §3, p. 69 & Appendix, p. 75):
each vertex `v : V` forms a level-`0` `sleeping` singleton fragment, all edges are `basic`, and all
message counters are zero. -/
@[expose] def initFragState (V : Type*) [Fintype V] [DecidableEq V] : FragState V where
  fragments := Finset.univ.image fun v => ⟨{v}, 0, none, .sleeping⟩
  branchEdges := ∅
  rejectedEdges := ∅
  msgs := {}

/-! ### Symmetry-preserving cut helpers and BFS `Change-root` hop counter -/

/-- Computable Boolean check testing whether both endpoints of `e` belong to `S`. -/
@[expose] def bothIn {V : Type*} [DecidableEq V] (S : Finset V) (e : Sym2 V) : Bool :=
  Sym2.lift
    ⟨fun u v => decide (u ∈ S) && decide (v ∈ S),
      fun u v => by dsimp only; cases decide (u ∈ S) <;> cases decide (v ∈ S) <;> rfl⟩
    e

@[simp]
private theorem bothIn_mk {V : Type*} [DecidableEq V] (S : Finset V) (u v : V) :
    bothIn S s(u, v) = (decide (u ∈ S) && decide (v ∈ S)) :=
  rfl

private theorem bothIn_eq_true_iff {V : Type*} [DecidableEq V] (S : Finset V) (e : Sym2 V) :
    bothIn S e = true ↔ ∀ x ∈ e, x ∈ S := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, Sym2.mem_iff]
    exact ⟨fun ⟨hu, hv⟩ x hx => hx.elim (· ▸ hu) (· ▸ hv),
      fun h => ⟨h u (.inl rfl), h v (.inr rfl)⟩⟩

/-- Computable Boolean check testing whether `e` has one endpoint in `S₁` and one in `S₂`. -/
@[expose] def betweenSets {V : Type*} [DecidableEq V] (S₁ S₂ : Finset V) (e : Sym2 V) : Bool :=
  Sym2.lift
    ⟨fun u v => (decide (u ∈ S₁) && decide (v ∈ S₂)) || (decide (u ∈ S₂) && decide (v ∈ S₁)),
      fun u v => by
        dsimp only
        cases decide (u ∈ S₁) <;> cases decide (v ∈ S₂) <;>
          cases decide (u ∈ S₂) <;> cases decide (v ∈ S₁) <;> rfl⟩
    e

@[simp]
private theorem betweenSets_mk {V : Type*} [DecidableEq V] (S₁ S₂ : Finset V) (u v : V) :
    betweenSets S₁ S₂ s(u, v) =
      ((decide (u ∈ S₁) && decide (v ∈ S₂)) || (decide (u ∈ S₂) && decide (v ∈ S₁))) :=
  rfl

private theorem betweenSets_eq_true_iff {V : Type*} [DecidableEq V] (S₁ S₂ : Finset V)
    (e : Sym2 V) :
    betweenSets S₁ S₂ e = true ↔ ∃ u ∈ S₁, ∃ v ∈ S₂, e = s(u, v) := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [betweenSets_mk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact ⟨x, hx, y, hy, rfl⟩
      · exact ⟨y, hy, x, hx, Sym2.eq_swap⟩
    · rintro ⟨u, hu, v, hv, heq⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .inl ⟨hu, hv⟩
      · exact .inr ⟨hv, hu⟩

/-- Whether all internal edges of `S` in `G` are non-`Basic` (`Branch` or `Rejected`). -/
@[expose] def noBasicInternalEdges {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (s : FragState V) (S : Finset V) : Bool :=
  decide (∀ c ∈ G.edgeFinset, bothIn S c = true → s.edgeState c ≠ .basic)

private theorem noBasicInternalEdges_eq_true_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (s : FragState V) (S : Finset V) :
    noBasicInternalEdges G s S = true ↔
      ∀ c ∈ G.edgeFinset, bothIn S c = true → s.edgeState c ≠ .basic := by
  unfold noBasicInternalEdges
  exact decide_eq_true_iff

/-- Number of vertices in `S` incident to at least one outgoing edge of `S` in `G` (each such
vertex transmits one successful `Test` and receives one `Accept` during a non-final search cycle,
[GallagerHumbletSpira1983], §4, p. 73). -/
@[expose] def outgoingNodeCount {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (S.filter fun u => ∃ v : V, G.Adj u v ∧ v ∉ S).card

private theorem outgoingNodeCount_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    outgoingNodeCount G S ≤ S.card :=
  Finset.card_filter_le _ _

/-- GHS `Test`/`Accept` level-delay guard ([GallagerHumbletSpira1983], §3, p. 71 and Appendix rule
(6), p. 76): every minimum-weight outgoing edge incident to any vertex `u ∈ F.verts` leads to a
fragment in `s.fragments` whose level is at least `F.level`. -/
@[expose] def allNodeMOEsAccepted {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) (s : FragState V)
    (F : Fragment V) : Bool :=
  decide (∀ u ∈ F.verts, ∀ v : V, G.Adj u v → v ∉ F.verts →
    (∀ v' : V, G.Adj u v' → v' ∉ F.verts → w s(u, v) ≤ w s(u, v')) →
    ∃ F' ∈ s.fragments, v ∈ F'.verts ∧ F.level ≤ F'.level)

/-- Computable BFS hop counter along `B` inside `verts` from `visited` to `target` with fuel `k`. -/
@[expose] def bfsDist {V : Type*} [DecidableEq V] (B : Finset (Sym2 V))
    (verts target : Finset V) : ℕ → Finset V → ℕ
  | 0, _ => 0
  | k + 1, visited =>
    if (visited ∩ target).Nonempty then 0
    else
      let next := visited ∪ verts.filter fun y => ∃ x ∈ visited, s(x, y) ∈ B
      1 + bfsDist B verts target k next

private theorem bfsDist_le {V : Type*} [DecidableEq V] (B : Finset (Sym2 V))
    (verts target : Finset V) (k : ℕ) (visited : Finset V) :
    bfsDist B verts target k visited ≤ k := by
  induction k generalizing visited with
  | zero => exact le_rfl
  | succ k ih =>
    unfold bfsDist
    split_ifs
    · exact Nat.zero_le _
    · dsimp only
      have := ih (visited ∪ verts.filter fun y => ∃ x ∈ visited, s(x, y) ∈ B)
      omega

/-- Number of `Change-root` (`Change-core`) messages sent from `F.core` toward the endpoint of `e`
in `F.verts` ([GallagerHumbletSpira1983], §3, p. 72). -/
@[expose] def changeRootHops {V : Type*} [DecidableEq V] (s : FragState V) (F : Fragment V)
    (e : Sym2 V) : ℕ :=
  let coreEnds := F.verts.filter fun x => F.core.elim false (fun c => decide (x ∈ c)) = true
  let moeEnds := F.verts.filter fun x => x ∈ e
  bfsDist s.branchEdges F.verts moeEnds (F.verts.card - 1) coreEnds

private theorem changeRootHops_add_one_le_card {V : Type*} [DecidableEq V] (s : FragState V)
    (F : Fragment V) (e : Sym2 V) (hne : F.verts.Nonempty) :
    changeRootHops s F e + 1 ≤ F.verts.card := by
  have hpos : 1 ≤ F.verts.card := Finset.card_pos.mpr hne
  have hle := bfsDist_le s.branchEdges F.verts (F.verts.filter fun x => x ∈ e)
    (F.verts.card - 1) (F.verts.filter fun x => F.core.elim false (fun c => decide (x ∈ c)) = true)
  dsimp only [changeRootHops]
  omega

/-! ### Executable fragment-phase transitions and `Cslib.LTS` -/

/-- Transition labels of the event-driven fragment-phase GHS protocol. -/
inductive FragAction (V : Type*) where
  /-- Wake up the sole vertex in a `1`-vertex graph (`0` outgoing edges, immediate halt). -/
  | wakeupSingleton (v : V)
  /-- Wake up sleeping singleton `{v}` and send `Connect(0)` over its minimum-weight incident edge
  `e` (Appendix rules (1)–(2), p. 75). -/
  | wakeup (v : V) (e : Sym2 V)
  /-- Reject an internal `Basic` chord `e` of searching fragment `F` via `Test` + `Reject`
  (`dual = false`) or simultaneous dual `Test` (`dual = true`, §3, p. 71). -/
  | rejectChord (F : Fragment V) (e : Sym2 V) (dual : Bool)
  /-- Complete the `Test`/`Accept`/`Report`/`Change-root`/`Connect` search cycle of non-spanning
  fragment `F`, discovering minimum-weight outgoing edge `e` (§3, pp. 71–72). -/
  | completeSearch (F : Fragment V) (e : Sym2 V)
  /-- Complete the final `Report(∞)` convergecast and halt once `F` spans `Finset.univ` and all
  internal `Basic` chords are rejected (§3, p. 71 & Appendix rule (10), p. 76). -/
  | haltSearch (F : Fragment V)
  /-- Absorb lower-level fragment `F₁` (`F₁.level < F₂.level`) along `F₁`'s MOE into `F₂`, keeping
  `F₂`'s level, core, and phase (`Find` or `Found`, §3, p. 72). -/
  | absorb (F₁ F₂ : Fragment V)
  /-- Merge equal-level fragments `F₁` and `F₂` (`F₁.level = F₂.level = L`) sharing mutual MOE `e`
  into a new searching fragment at level `L + 1` with core `some e` (§3, p. 72). -/
  | merge (F₁ F₂ : Fragment V) (e : Sym2 V)
  deriving @[expose] DecidableEq

/-- Whether an action combines two fragments (`absorb` or `merge`). -/
@[expose] def FragAction.isCombine {V : Type*} : FragAction V → Bool
  | .absorb _ _ | .merge _ _ _ => true
  | _ => false

/-- Executable single-step transition function of the fragment-phase GHS protocol. -/
@[expose] def fragStep? {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) (s : FragState V)
    (a : FragAction V) : Option (FragState V) :=
  match a with
  | .wakeupSingleton v =>
    let F : Fragment V := ⟨{v}, 0, none, .sleeping⟩
    if F ∈ s.fragments ∧ ({v} : Finset V) = Finset.univ then
      some { s with
        fragments := insert ⟨{v}, 0, none, .halted⟩ (s.fragments.erase F) }
    else none
  | .wakeup v e =>
    let F : Fragment V := ⟨{v}, 0, none, .sleeping⟩
    if F ∈ s.fragments ∧ IsMOE G w {v} e then
      some { s with
        fragments := insert ⟨{v}, 0, none, .found e⟩ (s.fragments.erase F)
        msgs := { s.msgs with connect := s.msgs.connect + 1 } }
    else none
  | .rejectChord F e dual =>
    if F ∈ s.fragments ∧ F.phase = .searching ∧ e ∈ G.edgeFinset ∧
        bothIn F.verts e = true ∧ s.edgeState e = .basic then
      let msgs' :=
        if dual then { s.msgs with test := s.msgs.test + 2 }
        else { s.msgs with test := s.msgs.test + 1, reject := s.msgs.reject + 1 }
      some { s with
        rejectedEdges := insert e s.rejectedEdges
        msgs := msgs' }
    else none
  | .completeSearch F e =>
    if F ∈ s.fragments ∧ F.phase = .searching ∧ F.verts ≠ Finset.univ ∧
        IsMOE G w F.verts e ∧ allNodeMOEsAccepted G w s F = true then
      let outK := outgoingNodeCount G F.verts
      let hops := changeRootHops s F e
      some { s with
        fragments := insert { F with phase := .found e } (s.fragments.erase F)
        msgs := { s.msgs with
          test := s.msgs.test + outK
          accept := s.msgs.accept + outK
          report := s.msgs.report + F.verts.card
          changeRoot := s.msgs.changeRoot + hops
          connect := s.msgs.connect + 1 } }
    else none
  | .haltSearch F =>
    if F ∈ s.fragments ∧ F.phase = .searching ∧ F.verts = Finset.univ ∧
        noBasicInternalEdges G s F.verts = true then
      some { s with
        fragments := insert { F with phase := .halted } (s.fragments.erase F)
        msgs := { s.msgs with report := s.msgs.report + F.verts.card } }
    else none
  | .absorb F₁ F₂ =>
    match F₁.phase with
    | .found e =>
      let okPhase₂ :=
        match F₂.phase with
        | .searching | .found _ => true
        | .sleeping | .halted => false
      if F₁ ∈ s.fragments ∧ F₂ ∈ s.fragments ∧ F₁ ≠ F₂ ∧ F₁.level < F₂.level ∧
          okPhase₂ = true ∧ betweenSets F₁.verts F₂.verts e = true then
        let F₂' : Fragment V := ⟨F₂.verts ∪ F₁.verts, F₂.level, F₂.core, F₂.phase⟩
        some { s with
          fragments := insert F₂' ((s.fragments.erase F₁).erase F₂)
          branchEdges := insert e s.branchEdges
          msgs := { s.msgs with initiate := s.msgs.initiate + F₁.verts.card } }
      else none
    | _ => none
  | .merge F₁ F₂ e =>
    if F₁ ∈ s.fragments ∧ F₂ ∈ s.fragments ∧ F₁ ≠ F₂ ∧ F₁.level = F₂.level ∧
        F₁.phase = .found e ∧ F₂.phase = .found e ∧
        betweenSets F₁.verts F₂.verts e = true then
      let F' : Fragment V := ⟨F₁.verts ∪ F₂.verts, F₁.level + 1, some e, .searching⟩
      some { s with
        fragments := insert F' ((s.fragments.erase F₁).erase F₂)
        branchEdges := insert e s.branchEdges
        msgs := { s.msgs with initiate := s.msgs.initiate + F₁.verts.card + F₂.verts.card } }
    else none

/-- Executable multi-step trace runner for `fragStep?`. -/
@[expose] def runFragTrace? {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) :
    FragState V → List (FragAction V) → Option (FragState V)
  | s, [] => some s
  | s, a :: as =>
    match fragStep? G w s a with
    | none => none
    | some s' => runFragTrace? G w s' as

/-- Labelled transition system of the event-driven fragment-phase GHS protocol. -/
@[expose] def fragLTS {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) :
    Cslib.LTS (FragState V) (FragAction V) where
  Tr s a s' := fragStep? G w s a = some s'

/-- `fragLTS` is deterministic since `fragStep?` is a function into `Option (FragState V)`. -/
instance deterministic_fragLTS {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) :
    (fragLTS G w).Deterministic where
  deterministic _ _ _ _ h₁ h₂ := Option.some.inj (h₁.symm.trans h₂)

theorem runFragTrace?_eq_some_iff_mTr {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W)
    (s : FragState V) (as : List (FragAction V)) (s' : FragState V) :
    runFragTrace? G w s as = some s' ↔ (fragLTS G w).MTr s as s' := by
  induction as generalizing s with
  | nil =>
    simp only [runFragTrace?, Option.some.injEq, Cslib.LTS.MTr.nil_iff]
  | cons a as ih =>
    simp only [runFragTrace?, Cslib.LTS.MTr.cons_iff]
    cases h : fragStep? G w s a with
    | none =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨s₁, htr, _⟩
      cases h.symm.trans htr
    | some s₁ =>
      rw [ih s₁]
      constructor
      · intro hmtr
        exact ⟨s₁, h, hmtr⟩
      · rintro ⟨s₂, htr, hmtr⟩
        have heq : s₁ = s₂ := Option.some.inj (h.symm.trans htr)
        exact heq ▸ hmtr

/-- Reachability from `initFragState V` in `fragLTS G w`. -/
@[expose] def FragReachable {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) (s : FragState V) : Prop :=
  (fragLTS G w).CanReach (initFragState V) s

theorem FragReachable.init {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) :
    FragReachable G w (initFragState V) :=
  ⟨[], .refl⟩

theorem FragReachable.step {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s s' : FragState V}
    {a : FragAction V} (hr : FragReachable G w s) (htr : (fragLTS G w).Tr s a s') :
    FragReachable G w s' := by
  obtain ⟨as, has⟩ := hr
  exact ⟨as ++ [a], has.stepR _ htr⟩

/-! ### Remaining message budget and inductive state invariant -/

/-- Remaining per-vertex non-rejection message budget at level threshold `L_max`. -/
private def perVertexBudget {V : Type*} (L_max level : ℕ) : FragPhase V → ℕ
  | .sleeping => 5 * (L_max - 1) + 3
  | .searching => 5 * (L_max - level) + 1
  | .found _ => if level < L_max then 5 * (L_max - 1 - level) + 2 else 0
  | .halted => 0

/-- Remaining non-rejection message budget of fragment `F` under maximum level `L_max`. -/
private def fragRemBudget {V : Type*} (L_max : ℕ) (F : Fragment V) : ℕ :=
  perVertexBudget L_max F.level F.phase * F.verts.card

/-- Inductive global invariant maintained by every reachable state of `fragLTS G w`. -/
private structure FragInv {V W : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) (s : FragState V) : Prop where
  verts_nonempty : ∀ F ∈ s.fragments, F.verts.Nonempty
  verts_disjoint : ∀ F₁ ∈ s.fragments, ∀ F₂ ∈ s.fragments, F₁ ≠ F₂ → Disjoint F₁.verts F₂.verts
  verts_cover : ∀ v : V, ∃ F ∈ s.fragments, v ∈ F.verts
  branch_sub : s.branchEdges ⊆ G.edgeFinset
  rejected_sub : s.rejectedEdges ⊆ G.edgeFinset
  branch_rejected_disjoint : Disjoint s.branchEdges s.rejectedEdges
  branch_isMOE : ∀ e ∈ s.branchEdges, ∃ S : Finset V, IsMOE G w S e
  branch_internal : ∀ e ∈ s.branchEdges, ∃ F ∈ s.fragments, bothIn F.verts e = true
  rejected_internal : ∀ e ∈ s.rejectedEdges, ∃ F ∈ s.fragments, bothIn F.verts e = true
  frag_branch_card : ∀ F ∈ s.fragments,
    (s.branchEdges.filter fun z => bothIn F.verts z = true).card + 1 = F.verts.card
  two_pow_level_le : ∀ F ∈ s.fragments, 2 ^ F.level ≤ F.verts.card
  sleeping_spec : ∀ F ∈ s.fragments, F.phase = .sleeping → ∃ v : V, F = ⟨{v}, 0, none, .sleeping⟩
  searching_level_pos : ∀ F ∈ s.fragments, F.phase = .searching → 1 ≤ F.level
  halted_spec : ∀ F ∈ s.fragments, F.phase = .halted →
    F.verts = Finset.univ ∧ G.edgeFinset ⊆ s.branchEdges ∪ s.rejectedEdges
  found_isMOE : ∀ F ∈ s.fragments, ∀ e, F.phase = .found e →
    F.verts ≠ Finset.univ ∧ IsMOE G w F.verts e
  found_target_level : ∀ F ∈ s.fragments, ∀ e, F.phase = .found e →
    ∃ F' ∈ s.fragments, F' ≠ F ∧ betweenSets F.verts F'.verts e = true ∧ F.level ≤ F'.level
  msgs_card_le_one : Fintype.card V ≤ 1 → s.msgs.total = 0
  msgs_budget : 2 ≤ Fintype.card V →
    let L_max := Nat.log 2 (Fintype.card V)
    s.msgs.total + 2 * (G.edgeFinset \ s.rejectedEdges).card +
        (∑ F ∈ s.fragments, fragRemBudget L_max F) ≤
      (5 * (L_max - 1) + 3) * Fintype.card V + 2 * G.edgeFinset.card

private theorem sum_verts_card_eq {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) :
    (∑ F ∈ s.fragments, F.verts.card) = Fintype.card V := by
  have hbi : s.fragments.biUnion Fragment.verts = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    exact hinv.verts_cover v
  rw [← Finset.card_univ, ← hbi, Finset.card_biUnion]
  intro F₁ h₁ F₂ h₂ hne
  exact hinv.verts_disjoint F₁ h₁ F₂ h₂ hne

private theorem notMem_erase_of_same_verts {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F F' : Fragment V} (hF : F ∈ s.fragments)
    (hsub : F.verts ⊆ F'.verts) :
    F' ∉ s.fragments.erase F := by
  intro hmem
  obtain ⟨hne, hF'_in⟩ := Finset.mem_erase.mp hmem
  obtain ⟨u, hu⟩ := hinv.verts_nonempty F hF
  exact Finset.disjoint_left.mp (hinv.verts_disjoint F' hF'_in F hF hne) (hsub hu) hu

private theorem notMem_erase2_of_union {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F₁ F₂ F' : Fragment V} (h₁ : F₁ ∈ s.fragments)
    (hsub : F₁.verts ⊆ F'.verts) :
    F' ∉ (s.fragments.erase F₁).erase F₂ := by
  intro hmem
  have hmem₁ : F' ∈ s.fragments.erase F₁ := Finset.mem_of_mem_erase hmem
  exact notMem_erase_of_same_verts hinv h₁ hsub hmem₁

private theorem level_le_log_of_inv {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F : Fragment V} (hF : F ∈ s.fragments) :
    F.level ≤ Nat.log 2 (Fintype.card V) := by
  have hpow : 2 ^ F.level ≤ Fintype.card V :=
    (hinv.two_pow_level_le F hF).trans (Finset.card_le_univ F.verts)
  exact Nat.le_log_of_pow_le (by decide) hpow

private theorem two_le_card_of_searching {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F : Fragment V} (hF : F ∈ s.fragments) (hph : F.phase = .searching) :
    2 ≤ Fintype.card V := by
  have hlev1 : 1 ≤ F.level := hinv.searching_level_pos F hF hph
  have hp := hinv.two_pow_level_le F hF
  have hc := Finset.card_le_univ F.verts
  have h2l : 2 ≤ 2 ^ F.level := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ F.level := Nat.pow_le_pow_right (by decide) hlev1
  omega

private theorem fragInv_init (V : Type*) {W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W) :
    FragInv G w (initFragState V) where
  verts_nonempty F hF := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    exact Finset.singleton_nonempty v
  verts_disjoint F₁ h₁ F₂ h₂ hne := by
    obtain ⟨v₁, -, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨v₂, -, rfl⟩ := Finset.mem_image.mp h₂
    rw [Finset.disjoint_singleton]
    intro heq
    exact hne (by rw [heq])
  verts_cover v := ⟨⟨{v}, 0, none, .sleeping⟩, Finset.mem_image_of_mem _ (Finset.mem_univ v),
    Finset.mem_singleton_self v⟩
  branch_sub := Finset.empty_subset _
  rejected_sub := Finset.empty_subset _
  branch_rejected_disjoint := disjoint_bot_left
  branch_isMOE _ he := absurd he (Finset.notMem_empty _)
  branch_internal _ he := absurd he (Finset.notMem_empty _)
  rejected_internal _ he := absurd he (Finset.notMem_empty _)
  frag_branch_card F hF := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    simp only [initFragState, Finset.filter_empty, Finset.card_empty, zero_add,
      Finset.card_singleton]
  two_pow_level_le F hF := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    simp only [pow_zero, Finset.card_singleton, le_rfl]
  sleeping_spec F hF _ := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨v, rfl⟩
  searching_level_pos F hF hphase := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    cases hphase
  halted_spec F hF hphase := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    cases hphase
  found_isMOE F hF _ hphase := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    cases hphase
  found_target_level F hF _ hphase := by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hF
    cases hphase
  msgs_card_le_one _ := rfl
  msgs_budget _ := by
    intro L_max
    have hsum : (∑ F ∈ (initFragState V).fragments, fragRemBudget L_max F) =
        (5 * (L_max - 1) + 3) * Fintype.card V := by
      simp only [initFragState]
      rw [Finset.sum_image]
      · simp only [fragRemBudget, perVertexBudget, Finset.card_singleton, mul_one,
          Finset.sum_const, Finset.card_univ, smul_eq_mul]
        exact Nat.mul_comm _ _
      · intro u _ v _ huv
        have hs : ({u} : Finset V) = {v} := congrArg Fragment.verts huv
        exact Finset.singleton_injective hs
    rw [hsum]
    simp only [initFragState, MsgCount.total, Finset.sdiff_empty]
    omega

/-- Helper for `absorb` and `merge`: combining two disjoint fragments `F₁ ≠ F₂` across a
cross-fragment edge `e ∈ G.edgeFinset` preserves `branch_isMOE`, `branch_internal`,
`rejected_internal`, and `frag_branch_card`. -/
private theorem combine_edge_facts {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F₁ F₂ Fcomb : Fragment V}
    (h₁ : F₁ ∈ s.fragments) (h₂ : F₂ ∈ s.fragments) (hne : F₁ ≠ F₂)
    (hverts : Fcomb.verts = F₁.verts ∪ F₂.verts)
    {e : Sym2 V} (hbtw : betweenSets F₁.verts F₂.verts e = true) :
    let frags' := insert Fcomb ((s.fragments.erase F₁).erase F₂)
    let branches' := insert e s.branchEdges
    e ∉ s.branchEdges ∧ e ∉ s.rejectedEdges ∧
      (∀ z ∈ branches', ∃ F ∈ frags', bothIn F.verts z = true) ∧
      (∀ z ∈ s.rejectedEdges, ∃ F ∈ frags', bothIn F.verts z = true) ∧
      (∀ F ∈ frags',
        (branches'.filter fun z => bothIn F.verts z = true).card + 1 = F.verts.card) := by
  intro frags' branches'
  obtain ⟨u₀, hu₀, v₀, hv₀, he_eq⟩ := (betweenSets_eq_true_iff F₁.verts F₂.verts e).mp hbtw
  have hdisj₁₂ : Disjoint F₁.verts F₂.verts := hinv.verts_disjoint F₁ h₁ F₂ h₂ hne
  have not_both_single : ∀ F ∈ s.fragments, bothIn F.verts e = false := by
    intro F hF
    rw [Bool.eq_false_iff]
    intro hboth
    rw [he_eq, bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hboth
    have heq₁ : F = F₁ := by
      by_contra hne₁
      exact Finset.disjoint_left.mp (hinv.verts_disjoint F hF F₁ h₁ hne₁) hboth.1 hu₀
    have heq₂ : F = F₂ := by
      by_contra hne₂
      exact Finset.disjoint_left.mp (hinv.verts_disjoint F hF F₂ h₂ hne₂) hboth.2 hv₀
    exact hne (heq₁.symm.trans heq₂)
  have he_not_branch : e ∉ s.branchEdges := by
    intro hm
    obtain ⟨F, hF, hb⟩ := hinv.branch_internal e hm
    rw [not_both_single F hF] at hb
    cases hb
  have he_not_rej : e ∉ s.rejectedEdges := by
    intro hm
    obtain ⟨F, hF, hb⟩ := hinv.rejected_internal e hm
    rw [not_both_single F hF] at hb
    cases hb
  have bothIn_mono : ∀ {A B : Finset V} {z : Sym2 V}, A ⊆ B → bothIn A z = true →
      bothIn B z = true := by
    intro A B z hAB hz
    rw [bothIn_eq_true_iff] at hz ⊢
    exact fun x hx => hAB (hz x hx)
  have lift_internal : ∀ z : Sym2 V, (∃ F ∈ s.fragments, bothIn F.verts z = true) →
      ∃ F ∈ frags', bothIn F.verts z = true := by
    rintro z ⟨F, hF, hz⟩
    by_cases hF₁ : F = F₁
    · refine ⟨Fcomb, Finset.mem_insert_self _ _, bothIn_mono ?_ (hF₁ ▸ hz)⟩
      rw [hverts]; exact Finset.subset_union_left
    · by_cases hF₂ : F = F₂
      · refine ⟨Fcomb, Finset.mem_insert_self _ _, bothIn_mono ?_ (hF₂ ▸ hz)⟩
        rw [hverts]; exact Finset.subset_union_right
      · refine ⟨F, Finset.mem_insert_of_mem ?_, hz⟩
        exact Finset.mem_erase.mpr ⟨hF₂, Finset.mem_erase.mpr ⟨hF₁, hF⟩⟩
  have hbr_int' : ∀ z ∈ branches', ∃ F ∈ frags', bothIn F.verts z = true := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz_old
    · refine ⟨Fcomb, Finset.mem_insert_self _ _, ?_⟩
      rw [he_eq, hverts, bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨Finset.mem_union_left _ hu₀, Finset.mem_union_right _ hv₀⟩
    · exact lift_internal z (hinv.branch_internal z hz_old)
  have hrej_int' : ∀ z ∈ s.rejectedEdges, ∃ F ∈ frags', bothIn F.verts z = true :=
    fun z hz => lift_internal z (hinv.rejected_internal z hz)
  have hcard' : ∀ F ∈ frags',
      (branches'.filter fun z => bothIn F.verts z = true).card + 1 = F.verts.card := by
    intro F hF
    rcases Finset.mem_insert.mp hF with hF_eq | hF_rest
    · subst F
      have he_both : bothIn Fcomb.verts e = true := by
        rw [he_eq, hverts, bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨Finset.mem_union_left _ hu₀, Finset.mem_union_right _ hv₀⟩
      have hfilt_ins : (branches'.filter fun z => bothIn Fcomb.verts z = true) =
          insert e (s.branchEdges.filter fun z => bothIn Fcomb.verts z = true) := by
        simp only [branches', Finset.filter_insert, he_both, ↓reduceIte]
      have he_not_filt : e ∉ s.branchEdges.filter fun z => bothIn Fcomb.verts z = true :=
        fun hm => he_not_branch (Finset.mem_of_mem_filter e hm)
      have hsplit : (s.branchEdges.filter fun z => bothIn Fcomb.verts z = true) =
          (s.branchEdges.filter fun z => bothIn F₁.verts z = true) ∪
            (s.branchEdges.filter fun z => bothIn F₂.verts z = true) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hzB, hzC⟩
          obtain ⟨F₀, hF₀, hz₀⟩ := hinv.branch_internal z hzB
          induction z using Sym2.ind with
          | _ a b =>
            rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hz₀ hzC
            rw [hverts, Finset.mem_union] at hzC
            rcases hzC.1 with ha₁ | ha₂
            · have hF₀_eq : F₀ = F₁ := by
                by_contra hne₀
                exact Finset.disjoint_left.mp (hinv.verts_disjoint F₀ hF₀ F₁ h₁ hne₀) hz₀.1 ha₁
              subst hF₀_eq
              left
              rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
              exact ⟨hzB, hz₀⟩
            · have hF₀_eq : F₀ = F₂ := by
                by_contra hne₀
                exact Finset.disjoint_left.mp (hinv.verts_disjoint F₀ hF₀ F₂ h₂ hne₀) hz₀.1 ha₂
              subst hF₀_eq
              right
              rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
              exact ⟨hzB, hz₀⟩
        · rintro (⟨hzB, hz₁⟩ | ⟨hzB, hz₂⟩)
          · exact ⟨hzB, bothIn_mono (hverts ▸ Finset.subset_union_left) hz₁⟩
          · exact ⟨hzB, bothIn_mono (hverts ▸ Finset.subset_union_right) hz₂⟩
      have hdisj_filt : Disjoint (s.branchEdges.filter fun z => bothIn F₁.verts z = true)
          (s.branchEdges.filter fun z => bothIn F₂.verts z = true) := by
        rw [Finset.disjoint_left]
        intro z hz₁ hz₂
        induction z using Sym2.ind with
        | _ a b =>
          have h₁' := (Finset.mem_filter.mp hz₁).2
          have h₂' := (Finset.mem_filter.mp hz₂).2
          rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h₁' h₂'
          exact Finset.disjoint_left.mp hdisj₁₂ h₁'.1 h₂'.1
      have hc₁ := hinv.frag_branch_card F₁ h₁
      have hc₂ := hinv.frag_branch_card F₂ h₂
      have hucard : Fcomb.verts.card = F₁.verts.card + F₂.verts.card := by
        rw [hverts, Finset.card_union_of_disjoint hdisj₁₂]
      rw [hfilt_ins, Finset.card_insert_of_notMem he_not_filt, hsplit,
        Finset.card_union_of_disjoint hdisj_filt]
      omega
    · have hF_in : F ∈ s.fragments := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hF_rest)
      have hfilt_eq : (branches'.filter fun z => bothIn F.verts z = true) =
          (s.branchEdges.filter fun z => bothIn F.verts z = true) := by
        simp only [branches', Finset.filter_insert, not_both_single F hF_in, Bool.false_eq_true,
          ↓reduceIte]
      rw [hfilt_eq]
      exact hinv.frag_branch_card F hF_in
  exact ⟨he_not_branch, he_not_rej, hbr_int', hrej_int', hcard'⟩

/-- Helper for single-fragment phase updates (`wakeupSingleton`, `wakeup`, `completeSearch`,
`haltSearch`) where `verts` and `level` are unchanged. -/
private theorem replace_phase_partition {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F F' : Fragment V} (hF : F ∈ s.fragments)
    (hverts : F'.verts = F.verts) (hlevel : F'.level = F.level) :
    let frags' := insert F' (s.fragments.erase F)
    F' ∉ s.fragments.erase F ∧
      (∀ G₀ ∈ frags', G₀.verts.Nonempty) ∧
      (∀ G₁ ∈ frags', ∀ G₂ ∈ frags', G₁ ≠ G₂ → Disjoint G₁.verts G₂.verts) ∧
      (∀ v : V, ∃ G₀ ∈ frags', v ∈ G₀.verts) ∧
      (∀ z ∈ s.branchEdges, ∃ G₀ ∈ frags', bothIn G₀.verts z = true) ∧
      (∀ z ∈ s.rejectedEdges, ∃ G₀ ∈ frags', bothIn G₀.verts z = true) ∧
      (∀ G₀ ∈ frags',
        (s.branchEdges.filter fun z => bothIn G₀.verts z = true).card + 1 = G₀.verts.card) ∧
      (∀ G₀ ∈ frags', 2 ^ G₀.level ≤ G₀.verts.card) := by
  intro frags'
  have hnotMem : F' ∉ s.fragments.erase F :=
    notMem_erase_of_same_verts hinv hF (by rw [hverts])
  refine ⟨hnotMem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G₀ hG₀
    rcases Finset.mem_insert.mp hG₀ with rfl | hG₀_er
    · rw [hverts]; exact hinv.verts_nonempty F hF
    · exact hinv.verts_nonempty G₀ (Finset.mem_of_mem_erase hG₀_er)
  · intro G₁ hG₁ G₂ hG₂ hne
    rcases Finset.mem_insert.mp hG₁ with rfl | h₁_er <;>
      rcases Finset.mem_insert.mp hG₂ with rfl | h₂_er
    · exact absurd rfl hne
    · obtain ⟨hne₂F, h₂_in⟩ := Finset.mem_erase.mp h₂_er
      rw [hverts]
      exact hinv.verts_disjoint F hF G₂ h₂_in hne₂F.symm
    · obtain ⟨hne₁F, h₁_in⟩ := Finset.mem_erase.mp h₁_er
      rw [hverts]
      exact hinv.verts_disjoint G₁ h₁_in F hF hne₁F
    · exact hinv.verts_disjoint G₁ (Finset.mem_of_mem_erase h₁_er)
        G₂ (Finset.mem_of_mem_erase h₂_er) hne
  · intro v
    obtain ⟨G₀, hG₀, hv⟩ := hinv.verts_cover v
    by_cases hGF : G₀ = F
    · exact ⟨F', Finset.mem_insert_self _ _, hverts ▸ hGF ▸ hv⟩
    · exact ⟨G₀, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hGF, hG₀⟩), hv⟩
  · intro z hz
    obtain ⟨G₀, hG₀, hb⟩ := hinv.branch_internal z hz
    by_cases hGF : G₀ = F
    · exact ⟨F', Finset.mem_insert_self _ _, hverts ▸ hGF ▸ hb⟩
    · exact ⟨G₀, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hGF, hG₀⟩), hb⟩
  · intro z hz
    obtain ⟨G₀, hG₀, hb⟩ := hinv.rejected_internal z hz
    by_cases hGF : G₀ = F
    · exact ⟨F', Finset.mem_insert_self _ _, hverts ▸ hGF ▸ hb⟩
    · exact ⟨G₀, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hGF, hG₀⟩), hb⟩
  · intro G₀ hG₀
    rcases Finset.mem_insert.mp hG₀ with rfl | hG₀_er
    · rw [hverts]; exact hinv.frag_branch_card F hF
    · exact hinv.frag_branch_card G₀ (Finset.mem_of_mem_erase hG₀_er)
  · intro G₀ hG₀
    rcases Finset.mem_insert.mp hG₀ with rfl | hG₀_er
    · rw [hverts, hlevel]; exact hinv.two_pow_level_le F hF
    · exact hinv.two_pow_level_le G₀ (Finset.mem_of_mem_erase hG₀_er)

/-- Helper for `absorb` and `merge`: replacing two distinct fragments `F₁ ≠ F₂` by `Fcomb` with
`Fcomb.verts = F₁.verts ∪ F₂.verts` preserves the fragment partition of `V`. -/
private theorem combine_partition {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) {F₁ F₂ Fcomb : Fragment V}
    (h₁ : F₁ ∈ s.fragments) (h₂ : F₂ ∈ s.fragments)
    (hverts : Fcomb.verts = F₁.verts ∪ F₂.verts) :
    let frags' := insert Fcomb ((s.fragments.erase F₁).erase F₂)
    Fcomb ∉ (s.fragments.erase F₁).erase F₂ ∧
      (∀ G₀ ∈ frags', G₀.verts.Nonempty) ∧
      (∀ G₁ ∈ frags', ∀ G₂ ∈ frags', G₁ ≠ G₂ → Disjoint G₁.verts G₂.verts) ∧
      (∀ v : V, ∃ G₀ ∈ frags', v ∈ G₀.verts) := by
  intro frags'
  have hnotMem : Fcomb ∉ (s.fragments.erase F₁).erase F₂ :=
    notMem_erase2_of_union hinv h₁ (hverts ▸ Finset.subset_union_left)
  refine ⟨hnotMem, ?_, ?_, ?_⟩
  · intro G₀ hG₀
    rcases Finset.mem_insert.mp hG₀ with rfl | hG₀_er
    · rw [hverts]; exact (hinv.verts_nonempty F₁ h₁).mono Finset.subset_union_left
    · exact hinv.verts_nonempty G₀ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hG₀_er))
  · intro G₁ hG₁ G₂ hG₂ hneG
    rcases Finset.mem_insert.mp hG₁ with rfl | h₁_er <;>
      rcases Finset.mem_insert.mp hG₂ with rfl | h₂_er
    · exact absurd rfl hneG
    · obtain ⟨hne₂₂, h₂_er₁⟩ := Finset.mem_erase.mp h₂_er
      obtain ⟨hne₂₁, h₂_in⟩ := Finset.mem_erase.mp h₂_er₁
      rw [hverts, Finset.disjoint_union_left]
      exact ⟨hinv.verts_disjoint F₁ h₁ G₂ h₂_in hne₂₁.symm,
        hinv.verts_disjoint F₂ h₂ G₂ h₂_in hne₂₂.symm⟩
    · obtain ⟨hne₁₂, h₁_er₁⟩ := Finset.mem_erase.mp h₁_er
      obtain ⟨hne₁₁, h₁_in⟩ := Finset.mem_erase.mp h₁_er₁
      rw [hverts, Finset.disjoint_union_right]
      exact ⟨hinv.verts_disjoint G₁ h₁_in F₁ h₁ hne₁₁,
        hinv.verts_disjoint G₁ h₁_in F₂ h₂ hne₁₂⟩
    · exact hinv.verts_disjoint G₁ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h₁_er))
        G₂ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h₂_er)) hneG
  · intro v
    obtain ⟨G₀, hG₀, hv⟩ := hinv.verts_cover v
    by_cases hG₁ : G₀ = F₁
    · exact ⟨Fcomb, Finset.mem_insert_self _ _, hverts ▸ Finset.mem_union_left _ (hG₁ ▸ hv)⟩
    · by_cases hG₂ : G₀ = F₂
      · exact ⟨Fcomb, Finset.mem_insert_self _ _, hverts ▸ Finset.mem_union_right _ (hG₂ ▸ hv)⟩
      · exact ⟨G₀, Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hG₂, Finset.mem_erase.mpr ⟨hG₁, hG₀⟩⟩), hv⟩

private theorem sum_erase2 {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) (f : α → ℕ) :
    (∑ x ∈ (s.erase a).erase b, f x) + f a + f b = ∑ x ∈ s, f x := by
  have hb_er : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hne.symm, hb⟩
  have h1 := Finset.sum_erase_add (s.erase a) f hb_er
  have h2 := Finset.sum_erase_add s f ha
  omega

private theorem fragInv_step {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s s' : FragState V}
    {a : FragAction V} (hinv : FragInv G w s) (htr : fragStep? G w s a = some s') :
    FragInv G w s' := by
  cases a with
  | wakeupSingleton v =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨hF, huniv⟩ := hg
    injection htr with hs'
    subst hs'
    let F : Fragment V := ⟨{v}, 0, none, .sleeping⟩
    let F' : Fragment V := ⟨{v}, 0, none, .halted⟩
    obtain ⟨hnotMem, hnemp, hdisj, hcov, hbr_int, hrej_int, hbr_card, hpow⟩ :=
      replace_phase_partition hinv hF (F' := F') rfl rfl
    have hcard_one : Fintype.card V = 1 := by
      rw [← Finset.card_univ, ← huniv, Finset.card_singleton]
    have hG_empty : G.edgeFinset = ∅ := by
      ext e
      simp only [mem_edgeFinset, Finset.notMem_empty, iff_false]
      intro he
      induction e using Sym2.ind with
      | _ x y =>
        have hx : x ∈ ({v} : Finset V) := huniv.symm ▸ Finset.mem_univ x
        have hy : y ∈ ({v} : Finset V) := huniv.symm ▸ Finset.mem_univ y
        rw [Finset.mem_singleton] at hx hy
        exact (G.mem_edgeSet.mp he).ne (hx.trans hy.symm)
    refine
      { verts_nonempty := hnemp
        verts_disjoint := hdisj
        verts_cover := hcov
        branch_sub := hinv.branch_sub
        rejected_sub := hinv.rejected_sub
        branch_rejected_disjoint := hinv.branch_rejected_disjoint
        branch_isMOE := hinv.branch_isMOE
        branch_internal := hbr_int
        rejected_internal := hrej_int
        frag_branch_card := hbr_card
        two_pow_level_le := hpow
        sleeping_spec := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.sleeping_spec G₀ (Finset.mem_of_mem_erase h_er) hph
        searching_level_pos := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.searching_level_pos G₀ (Finset.mem_of_mem_erase h_er) hph
        halted_spec := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · exact ⟨huniv, by rw [hG_empty]; exact Finset.empty_subset _⟩
          · exact hinv.halted_spec G₀ (Finset.mem_of_mem_erase h_er) hph
        found_isMOE := fun G₀ hG₀ e₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.found_isMOE G₀ (Finset.mem_of_mem_erase h_er) e₀ hph
        found_target_level := fun G₀ hG₀ e₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · obtain ⟨hne₀, hG₀_in⟩ := Finset.mem_erase.mp h_er
            obtain ⟨u, hu⟩ := hinv.verts_nonempty G₀ hG₀_in
            have hu_v : u ∈ ({v} : Finset V) := huniv.symm ▸ Finset.mem_univ u
            exact absurd hu_v (Finset.disjoint_left.mp (hinv.verts_disjoint G₀ hG₀_in F hF hne₀) hu)
        msgs_card_le_one := hinv.msgs_card_le_one
        msgs_budget := fun h2 => by omega }
  | wakeup v e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨hF, hmoe⟩ := hg
    injection htr with hs'
    subst hs'
    let F : Fragment V := ⟨{v}, 0, none, .sleeping⟩
    let F' : Fragment V := ⟨{v}, 0, none, .found e⟩
    obtain ⟨hnotMem, hnemp, hdisj, hcov, hbr_int, hrej_int, hbr_card, hpow⟩ :=
      replace_phase_partition hinv hF (F' := F') rfl rfl
    obtain ⟨_, u₀, hu₀, w₀, hw₀, he_eq⟩ := hmoe.1
    rw [Finset.mem_singleton] at hu₀
    subst u₀
    have hnot_univ : ({v} : Finset V) ≠ Finset.univ := fun hu => hw₀ (hu ▸ Finset.mem_univ w₀)
    have hcard2 : 2 ≤ Fintype.card V := by
      have hvw : v ≠ w₀ := fun h => hw₀ (h ▸ Finset.mem_singleton_self v)
      have hsub : ({v, w₀} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hvw, Finset.card_univ] at hc
      exact hc
    refine
      { verts_nonempty := hnemp
        verts_disjoint := hdisj
        verts_cover := hcov
        branch_sub := hinv.branch_sub
        rejected_sub := hinv.rejected_sub
        branch_rejected_disjoint := hinv.branch_rejected_disjoint
        branch_isMOE := hinv.branch_isMOE
        branch_internal := hbr_int
        rejected_internal := hrej_int
        frag_branch_card := hbr_card
        two_pow_level_le := hpow
        sleeping_spec := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.sleeping_spec G₀ (Finset.mem_of_mem_erase h_er) hph
        searching_level_pos := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.searching_level_pos G₀ (Finset.mem_of_mem_erase h_er) hph
        halted_spec := fun G₀ hG₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph
          · exact hinv.halted_spec G₀ (Finset.mem_of_mem_erase h_er) hph
        found_isMOE := fun G₀ hG₀ e₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · injection hph with he₀; subst he₀; exact ⟨hnot_univ, hmoe⟩
          · exact hinv.found_isMOE G₀ (Finset.mem_of_mem_erase h_er) e₀ hph
        found_target_level := fun G₀ hG₀ e₀ hph => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · injection hph with he₀; subst he₀
            obtain ⟨Ft, hFt, hw_in⟩ := hinv.verts_cover w₀
            have hFt_ne_F : Ft ≠ F := fun h =>
              hw₀ ((show Ft.verts = {v} from congrArg Fragment.verts h) ▸ hw_in)
            refine ⟨Ft, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hFt_ne_F, hFt⟩), ?_,
              ?_, Nat.zero_le _⟩
            · intro hFt_F'
              exact hw₀ ((show Ft.verts = {v} from congrArg Fragment.verts hFt_F') ▸ hw_in)
            · rw [betweenSets_eq_true_iff]
              exact ⟨v, Finset.mem_singleton_self v, w₀, hw_in, he_eq⟩
          · obtain ⟨hne₀, hG₀_in⟩ := Finset.mem_erase.mp h_er
            obtain ⟨Ft, hFt, hFt_ne, hbtw, hlev⟩ := hinv.found_target_level G₀ hG₀_in e₀ hph
            by_cases hFt_F : Ft = F
            · subst hFt_F
              refine ⟨F', Finset.mem_insert_self _ _, fun h => hnotMem (h ▸ h_er), hbtw, hlev⟩
            · exact ⟨Ft, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hFt_F, hFt⟩),
                hFt_ne, hbtw, hlev⟩
        msgs_card_le_one := fun h1 => by omega
        msgs_budget := fun h2 => by
          intro L_max
          have hL_pos : 1 ≤ L_max := Nat.le_log_of_pow_le (by decide) (by simpa using h2)
          have h0_lt : 0 < L_max := hL_pos
          have hsum_er := Finset.sum_erase_add s.fragments (fragRemBudget L_max) hF
          have hsum_ins := Finset.sum_insert hnotMem (f := fragRemBudget L_max)
          have hb_old : fragRemBudget L_max F = 5 * (L_max - 1) + 3 := by
            simp only [F, fragRemBudget, perVertexBudget, Finset.card_singleton, mul_one]
          have hb_new : fragRemBudget L_max F' = 5 * (L_max - 1) + 2 := by
            simp only [F', fragRemBudget, perVertexBudget, h0_lt, ↓reduceIte, Nat.sub_zero,
              Finset.card_singleton, mul_one]
          have htot : ({ s.msgs with connect := s.msgs.connect + 1 } : MsgCount).total =
              s.msgs.total + 1 := by
            simp only [MsgCount.total]; omega
          have hprev := hinv.msgs_budget h2
          dsimp only [L_max, F, F'] at *
          omega }
  | rejectChord F e dual =>
    dsimp only [fragStep?] at htr
    by_cases hg : F ∈ s.fragments ∧ F.phase = .searching ∧ e ∈ G.edgeFinset ∧
        bothIn F.verts e = true ∧ s.edgeState e = .basic
    · simp only [hg] at htr
      obtain ⟨hF, hph, he_fin, hboth, hbasic⟩ := hg
      injection htr with hs'
      subst hs'
      have he_not_br : e ∉ s.branchEdges := by
        intro hm; simp only [FragState.edgeState, hm, ↓reduceIte, reduceCtorEq] at hbasic
      have he_not_rej : e ∉ s.rejectedEdges := by
        intro hm; simp only [FragState.edgeState, he_not_br, hm, ↓reduceIte, reduceCtorEq] at hbasic
      have hcard2 : 2 ≤ Fintype.card V := two_le_card_of_searching hinv hF hph
      refine
        { verts_nonempty := hinv.verts_nonempty
          verts_disjoint := hinv.verts_disjoint
          verts_cover := hinv.verts_cover
          branch_sub := hinv.branch_sub
          rejected_sub := Finset.insert_subset he_fin hinv.rejected_sub
          branch_rejected_disjoint :=
            Finset.disjoint_insert_right.mpr ⟨he_not_br, hinv.branch_rejected_disjoint⟩
          branch_isMOE := hinv.branch_isMOE
          branch_internal := hinv.branch_internal
          rejected_internal := fun z hz => by
            rcases Finset.mem_insert.mp hz with rfl | hz_old
            · exact ⟨F, hF, hboth⟩
            · exact hinv.rejected_internal z hz_old
          frag_branch_card := hinv.frag_branch_card
          two_pow_level_le := hinv.two_pow_level_le
          sleeping_spec := hinv.sleeping_spec
          searching_level_pos := hinv.searching_level_pos
          halted_spec := fun G₀ hG₀ hph₀ => by
            obtain ⟨hu, hsub⟩ := hinv.halted_spec G₀ hG₀ hph₀
            exact ⟨hu, hsub.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))⟩
          found_isMOE := hinv.found_isMOE
          found_target_level := hinv.found_target_level
          msgs_card_le_one := fun h1 => by omega
          msgs_budget := fun h2 => by
            intro L_max
            have he_sdiff : e ∈ G.edgeFinset \ s.rejectedEdges :=
              Finset.mem_sdiff.mpr ⟨he_fin, he_not_rej⟩
            have hsdiff_eq : G.edgeFinset \ insert e s.rejectedEdges =
                (G.edgeFinset \ s.rejectedEdges).erase e := by
              ext z
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
              tauto
            have hcard_sd : (G.edgeFinset \ insert e s.rejectedEdges).card + 1 =
                (G.edgeFinset \ s.rejectedEdges).card := by
              rw [hsdiff_eq, Finset.card_erase_add_one he_sdiff]
            have htot : (if dual then { s.msgs with test := s.msgs.test + 2 }
                else { s.msgs with test := s.msgs.test + 1, reject := s.msgs.reject + 1 }).total =
                s.msgs.total + 2 := by
              cases dual <;> simp only [↓reduceIte, Bool.false_eq_true, MsgCount.total] <;> omega
            have hprev := hinv.msgs_budget h2
            dsimp only [L_max] at *
            omega }
    · simp only [hg] at htr
      cases htr
  | completeSearch F e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨hF, hph, hne_univ, hmoe, hallAcc⟩ := hg
    injection htr with hs'
    subst hs'
    let F' : Fragment V := { F with phase := .found e }
    obtain ⟨hnotMem, hnemp, hdisj, hcov, hbr_int, hrej_int, hbr_card, hpow⟩ :=
      replace_phase_partition hinv hF (F' := F') rfl rfl
    obtain ⟨hadj_edge, u₀, hu₀, v₀, hv₀, he_eq⟩ := hmoe.1
    have hadj_uv : G.Adj u₀ v₀ := G.mem_edgeSet.mp (he_eq ▸ hadj_edge)
    have hmin_uv : ∀ v', G.Adj u₀ v' → v' ∉ F.verts → w s(u₀, v₀) ≤ w s(u₀, v') := by
      intro v' hadj' hv'
      rw [← he_eq]
      exact hmoe.2 s(u₀, v') ⟨G.mem_edgeSet.mpr hadj', u₀, hu₀, v', hv', rfl⟩
    unfold allNodeMOEsAccepted at hallAcc
    have hallAcc' := of_decide_eq_true hallAcc
    obtain ⟨Ft, hFt, hv₀_Ft, hF_le_Ft⟩ := hallAcc' u₀ hu₀ v₀ hadj_uv hv₀ hmin_uv
    have hFt_ne_F : Ft ≠ F := fun h => hv₀ ((congrArg Fragment.verts h) ▸ hv₀_Ft)
    have hdisj_FFt : Disjoint F.verts Ft.verts := hinv.verts_disjoint F hF Ft hFt hFt_ne_F.symm
    have hF_lt_Lmax : F.level < Nat.log 2 (Fintype.card V) := by
      have hpF := hinv.two_pow_level_le F hF
      have hpFt := hinv.two_pow_level_le Ft hFt
      have hpFt' : 2 ^ F.level ≤ Ft.verts.card :=
        (Nat.pow_le_pow_right (by decide) hF_le_Ft).trans hpFt
      have hsum_le : F.verts.card + Ft.verts.card ≤ Fintype.card V := by
        rw [← Finset.card_union_of_disjoint hdisj_FFt]
        exact Finset.card_le_univ _
      have hpow_succ : 2 ^ (F.level + 1) ≤ Fintype.card V := by
        rw [Nat.pow_succ]
        omega
      have hle_succ := Nat.le_log_of_pow_le (by decide) hpow_succ
      omega
    have hcard2 : 2 ≤ Fintype.card V := two_le_card_of_searching hinv hF hph
    refine
      { verts_nonempty := hnemp
        verts_disjoint := hdisj
        verts_cover := hcov
        branch_sub := hinv.branch_sub
        rejected_sub := hinv.rejected_sub
        branch_rejected_disjoint := hinv.branch_rejected_disjoint
        branch_isMOE := hinv.branch_isMOE
        branch_internal := hbr_int
        rejected_internal := hrej_int
        frag_branch_card := hbr_card
        two_pow_level_le := hpow
        sleeping_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.sleeping_spec G₀ (Finset.mem_of_mem_erase h_er) hph₀
        searching_level_pos := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.searching_level_pos G₀ (Finset.mem_of_mem_erase h_er) hph₀
        halted_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.halted_spec G₀ (Finset.mem_of_mem_erase h_er) hph₀
        found_isMOE := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · injection hph₀ with he₀; subst he₀; exact ⟨hne_univ, hmoe⟩
          · exact hinv.found_isMOE G₀ (Finset.mem_of_mem_erase h_er) e₀ hph₀
        found_target_level := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · injection hph₀ with he₀; subst he₀
            refine ⟨Ft, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hFt_ne_F, hFt⟩), ?_, ?_,
              hF_le_Ft⟩
            · intro hFt_F'
              exact hv₀ ((congrArg Fragment.verts hFt_F') ▸ hv₀_Ft)
            · rw [betweenSets_eq_true_iff]
              exact ⟨u₀, hu₀, v₀, hv₀_Ft, he_eq⟩
          · obtain ⟨hne₀, hG₀_in⟩ := Finset.mem_erase.mp h_er
            obtain ⟨Gt, hGt, hGt_ne, hbtw, hlev⟩ := hinv.found_target_level G₀ hG₀_in e₀ hph₀
            by_cases hGt_F : Gt = F
            · subst hGt_F
              exact ⟨F', Finset.mem_insert_self _ _, fun h => hnotMem (h ▸ h_er), hbtw, hlev⟩
            · exact ⟨Gt, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hGt_F, hGt⟩),
                hGt_ne, hbtw, hlev⟩
        msgs_card_le_one := fun h1 => by omega
        msgs_budget := fun h2 => by
          intro L_max
          have hsum_er := Finset.sum_erase_add s.fragments (fragRemBudget L_max) hF
          have hsum_ins := Finset.sum_insert hnotMem (f := fragRemBudget L_max)
          have hout_le : outgoingNodeCount G F.verts ≤ F.verts.card :=
            outgoingNodeCount_le_card G F.verts
          have hhops_le : changeRootHops s F e + 1 ≤ F.verts.card :=
            changeRootHops_add_one_le_card s F e (hinv.verts_nonempty F hF)
          have hlt_L : F.level < L_max := hF_lt_Lmax
          have hb_diff : fragRemBudget L_max F =
              fragRemBudget L_max F' + 4 * F.verts.card := by
            simp only [F', hph, fragRemBudget, perVertexBudget, hlt_L, ↓reduceIte]
            have h1 : 5 * (L_max - F.level) + 1 = 5 * (L_max - 1 - F.level) + 2 + 4 := by omega
            rw [h1, Nat.right_distrib]
          have htot : ({ s.msgs with
              test := s.msgs.test + outgoingNodeCount G F.verts
              accept := s.msgs.accept + outgoingNodeCount G F.verts
              report := s.msgs.report + F.verts.card
              changeRoot := s.msgs.changeRoot + changeRootHops s F e
              connect := s.msgs.connect + 1 } : MsgCount).total ≤
              s.msgs.total + 4 * F.verts.card := by
            simp only [MsgCount.total]; omega
          have hprev := hinv.msgs_budget h2
          dsimp only [L_max, F'] at *
          omega }
  | haltSearch F =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨hF, hph, huniv, hnoBasic⟩ := hg
    injection htr with hs'
    subst hs'
    let F' : Fragment V := { F with phase := .halted }
    obtain ⟨hnotMem, hnemp, hdisj, hcov, hbr_int, hrej_int, hbr_card, hpow⟩ :=
      replace_phase_partition hinv hF (F' := F') rfl rfl
    have hcard2 : 2 ≤ Fintype.card V := two_le_card_of_searching hinv hF hph
    have hall_classified : G.edgeFinset ⊆ s.branchEdges ∪ s.rejectedEdges := by
      intro c hc
      have hnoB := (noBasicInternalEdges_eq_true_iff G s F.verts).mp hnoBasic
      have hboth : bothIn F.verts c = true := by
        rw [huniv, bothIn_eq_true_iff]
        exact fun x _ => Finset.mem_univ x
      have h1 := hnoB c hc hboth
      simp only [FragState.edgeState] at h1
      by_cases hbr : c ∈ s.branchEdges
      · exact Finset.mem_union_left _ hbr
      · by_cases hrej : c ∈ s.rejectedEdges
        · exact Finset.mem_union_right _ hrej
        · simp only [hbr, hrej, ↓reduceIte, ne_eq, not_true_eq_false] at h1
    refine
      { verts_nonempty := hnemp
        verts_disjoint := hdisj
        verts_cover := hcov
        branch_sub := hinv.branch_sub
        rejected_sub := hinv.rejected_sub
        branch_rejected_disjoint := hinv.branch_rejected_disjoint
        branch_isMOE := hinv.branch_isMOE
        branch_internal := hbr_int
        rejected_internal := hrej_int
        frag_branch_card := hbr_card
        two_pow_level_le := hpow
        sleeping_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.sleeping_spec G₀ (Finset.mem_of_mem_erase h_er) hph₀
        searching_level_pos := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.searching_level_pos G₀ (Finset.mem_of_mem_erase h_er) hph₀
        halted_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · exact ⟨huniv, hall_classified⟩
          · exact hinv.halted_spec G₀ (Finset.mem_of_mem_erase h_er) hph₀
        found_isMOE := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.found_isMOE G₀ (Finset.mem_of_mem_erase h_er) e₀ hph₀
        found_target_level := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · obtain ⟨hne₀, hG₀_in⟩ := Finset.mem_erase.mp h_er
            obtain ⟨u, hu⟩ := hinv.verts_nonempty G₀ hG₀_in
            have huF : u ∈ F.verts := huniv.symm ▸ Finset.mem_univ u
            exact absurd huF (Finset.disjoint_left.mp (hinv.verts_disjoint G₀ hG₀_in F hF hne₀) hu)
        msgs_card_le_one := fun h1 => by omega
        msgs_budget := fun h2 => by
          intro L_max
          have hsum_er := Finset.sum_erase_add s.fragments (fragRemBudget L_max) hF
          have hsum_ins := Finset.sum_insert hnotMem (f := fragRemBudget L_max)
          have hb_new : fragRemBudget L_max F' = 0 := by
            simp only [F', fragRemBudget, perVertexBudget, zero_mul]
          have hb_old : F.verts.card ≤ fragRemBudget L_max F := by
            simp only [fragRemBudget, hph, perVertexBudget]
            exact Nat.le_mul_of_pos_left _ (by omega)
          have htot : ({ s.msgs with report := s.msgs.report + F.verts.card } : MsgCount).total =
              s.msgs.total + F.verts.card := by
            simp only [MsgCount.total]; omega
          have hprev := hinv.msgs_budget h2
          dsimp only [L_max, F'] at *
          omega }
  | absorb F₁ F₂ =>
    dsimp only [fragStep?] at htr
    cases hph₁ : F₁.phase with
    | sleeping | searching | halted =>
      rw [hph₁] at htr; cases htr
    | found e =>
      rw [hph₁] at htr
      dsimp only at htr
      split_ifs at htr with hg
      obtain ⟨h₁, h₂, hne, hlt, hok₂, hbtw⟩ := hg
      injection htr with hs'
      subst hs'
      let F₂' : Fragment V := ⟨F₂.verts ∪ F₁.verts, F₂.level, F₂.core, F₂.phase⟩
      have hverts_comm : F₂'.verts = F₁.verts ∪ F₂.verts := Finset.union_comm _ _
      obtain ⟨hnotMem, hnemp, hdisj, hcov⟩ :=
        combine_partition hinv h₁ h₂ (Fcomb := F₂') hverts_comm
      obtain ⟨_, hmoe₁⟩ := hinv.found_isMOE F₁ h₁ e hph₁
      have he_fin : e ∈ G.edgeFinset := mem_edgeFinset.mpr hmoe₁.1.1
      obtain ⟨he_not_br, he_not_rej, hbr_int, hrej_int, hbr_card⟩ :=
        combine_edge_facts hinv h₁ h₂ hne (Fcomb := F₂') hverts_comm hbtw
      have hdisj₁₂ : Disjoint F₁.verts F₂.verts := hinv.verts_disjoint F₁ h₁ F₂ h₂ hne
      have hcard2 : 2 ≤ Fintype.card V := by
        obtain ⟨u₁, hu₁⟩ := hinv.verts_nonempty F₁ h₁
        obtain ⟨u₂, hu₂⟩ := hinv.verts_nonempty F₂ h₂
        have hu_ne : u₁ ≠ u₂ := fun h => Finset.disjoint_left.mp hdisj₁₂ hu₁ (h ▸ hu₂)
        have hc := Finset.card_le_card (Finset.subset_univ ({u₁, u₂} : Finset V))
        rw [Finset.card_pair hu_ne, Finset.card_univ] at hc
        exact hc
      have hF₂_found_pres : ∀ e₂, F₂.phase = .found e₂ →
          F₂'.verts ≠ Finset.univ ∧ IsMOE G w F₂'.verts e₂ ∧
            ∃ Ft ∈ insert F₂' ((s.fragments.erase F₁).erase F₂),
              Ft ≠ F₂' ∧ betweenSets F₂'.verts Ft.verts e₂ = true ∧ F₂'.level ≤ Ft.level := by
        intro e₂ hph₂
        obtain ⟨_, hmoe₂⟩ := hinv.found_isMOE F₂ h₂ e₂ hph₂
        obtain ⟨F₃, h₃, h₃_ne_₂, hbtw₂, hlev₂₃⟩ := hinv.found_target_level F₂ h₂ e₂ hph₂
        have h₃_ne_₁ : F₃ ≠ F₁ := by
          intro h; subst h; omega
        obtain ⟨u₂, hu₂, v₂, hv₂, he₂_eq⟩ := (betweenSets_eq_true_iff _ _ _).mp hbtw₂
        have hv₂_not₂ : v₂ ∉ F₂.verts :=
          Finset.disjoint_right.mp (hinv.verts_disjoint F₂ h₂ F₃ h₃ h₃_ne_₂.symm) hv₂
        have hv₂_not₁ : v₂ ∉ F₁.verts :=
          Finset.disjoint_right.mp (hinv.verts_disjoint F₁ h₁ F₃ h₃ h₃_ne_₁.symm) hv₂
        have hv₂_not_u : v₂ ∉ F₂'.verts := by
          simp only [F₂', Finset.mem_union, not_or]; exact ⟨hv₂_not₂, hv₂_not₁⟩
        have hnot_univ' : F₂'.verts ≠ Finset.univ := fun hu => hv₂_not_u (hu ▸ Finset.mem_univ v₂)
        have hout_e₂ : IsOutgoingEdge G F₂'.verts e₂ :=
          ⟨hmoe₂.1.1, u₂, Finset.mem_union_left _ hu₂, v₂, hv₂_not_u, he₂_eq⟩
        obtain ⟨u₁, hu₁, v₁, hv₁, he₁_eq⟩ := (betweenSets_eq_true_iff _ _ _).mp hbtw
        have hu₁_not₂ : u₁ ∉ F₂.verts := Finset.disjoint_left.mp hdisj₁₂ hu₁
        have hout_e₁_from₂ : IsOutgoingEdge G F₂.verts e :=
          ⟨hmoe₁.1.1, v₁, hv₁, u₁, hu₁_not₂, he₁_eq.trans Sym2.eq_swap⟩
        have hw_e₂_le_e₁ : w e₂ ≤ w e := hmoe₂.2 e hout_e₁_from₂
        have hmoe₂' : IsMOE G w F₂'.verts e₂ := by
          refine ⟨hout_e₂, fun f hf => ?_⟩
          obtain ⟨hfG, a, ha, b, hb, hf_eq⟩ := hf
          simp only [F₂', Finset.mem_union, not_or] at ha hb
          rcases ha with ha₂ | ha₁
          · exact hmoe₂.2 f ⟨hfG, a, ha₂, b, hb.1, hf_eq⟩
          · exact hw_e₂_le_e₁.trans (hmoe₁.2 f ⟨hfG, a, ha₁, b, hb.2, hf_eq⟩)
        have h₃_in' : F₃ ∈ insert F₂' ((s.fragments.erase F₁).erase F₂) :=
          Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨h₃_ne_₂, Finset.mem_erase.mpr ⟨h₃_ne_₁, h₃⟩⟩)
        have h₃_ne_2' : F₃ ≠ F₂' := fun h => hv₂_not_u (h ▸ hv₂)
        have hbtw₂' : betweenSets F₂'.verts F₃.verts e₂ = true := by
          rw [betweenSets_eq_true_iff]
          exact ⟨u₂, Finset.mem_union_left _ hu₂, v₂, hv₂, he₂_eq⟩
        exact ⟨hnot_univ', hmoe₂', F₃, h₃_in', h₃_ne_2', hbtw₂', hlev₂₃⟩
      refine
        { verts_nonempty := hnemp
          verts_disjoint := hdisj
          verts_cover := hcov
          branch_sub := Finset.insert_subset he_fin hinv.branch_sub
          rejected_sub := hinv.rejected_sub
          branch_rejected_disjoint :=
            Finset.disjoint_insert_left.mpr ⟨he_not_rej, hinv.branch_rejected_disjoint⟩
          branch_isMOE := fun z hz => by
            rcases Finset.mem_insert.mp hz with rfl | hz_old
            · exact ⟨F₁.verts, hmoe₁⟩
            · exact hinv.branch_isMOE z hz_old
          branch_internal := hbr_int
          rejected_internal := hrej_int
          frag_branch_card := hbr_card
          two_pow_level_le := fun G₀ hG₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · exact (hinv.two_pow_level_le F₂ h₂).trans
                (Finset.card_le_card Finset.subset_union_left)
            · exact hinv.two_pow_level_le G₀
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er))
          sleeping_spec := fun G₀ hG₀ hph₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · change F₂.phase = .sleeping at hph₀; rw [hph₀] at hok₂; cases hok₂
            · exact hinv.sleeping_spec G₀
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
          searching_level_pos := fun G₀ hG₀ hph₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · exact hinv.searching_level_pos F₂ h₂ hph₀
            · exact hinv.searching_level_pos G₀
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
          halted_spec := fun G₀ hG₀ hph₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · change F₂.phase = .halted at hph₀; rw [hph₀] at hok₂; cases hok₂
            · obtain ⟨hu, hsub⟩ := hinv.halted_spec G₀
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
              exact ⟨hu, hsub.trans (Finset.union_subset_union_left (Finset.subset_insert _ _))⟩
          found_isMOE := fun G₀ hG₀ e₀ hph₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · obtain ⟨hnu, hm, _⟩ := hF₂_found_pres e₀ hph₀
              exact ⟨hnu, hm⟩
            · exact hinv.found_isMOE G₀
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) e₀ hph₀
          found_target_level := fun G₀ hG₀ e₀ hph₀ => by
            rcases Finset.mem_insert.mp hG₀ with rfl | h_er
            · exact (hF₂_found_pres e₀ hph₀).2.2
            · obtain ⟨hne₀₂, h_er₁⟩ := Finset.mem_erase.mp h_er
              obtain ⟨hne₀₁, hG₀_in⟩ := Finset.mem_erase.mp h_er₁
              obtain ⟨Gt, hGt, hGt_ne, hbtw₀, hlev₀⟩ := hinv.found_target_level G₀ hG₀_in e₀ hph₀
              obtain ⟨ua, hua, ub, hub, he₀_eq⟩ := (betweenSets_eq_true_iff _ _ _).mp hbtw₀
              have hF₂'_ne_G₀ : F₂' ≠ G₀ := fun h => hnotMem (h ▸ h_er)
              by_cases hGt₁ : Gt = F₁
              · subst hGt₁
                refine ⟨F₂', Finset.mem_insert_self _ _, hF₂'_ne_G₀, ?_, ?_⟩
                · rw [betweenSets_eq_true_iff]
                  exact ⟨ua, hua, ub, Finset.mem_union_right _ hub, he₀_eq⟩
                · dsimp only [F₂']; omega
              · by_cases hGt₂ : Gt = F₂
                · subst hGt₂
                  refine ⟨F₂', Finset.mem_insert_self _ _, hF₂'_ne_G₀, ?_, hlev₀⟩
                  rw [betweenSets_eq_true_iff]
                  exact ⟨ua, hua, ub, Finset.mem_union_left _ hub, he₀_eq⟩
                · exact ⟨Gt, Finset.mem_insert_of_mem
                    (Finset.mem_erase.mpr ⟨hGt₂, Finset.mem_erase.mpr ⟨hGt₁, hGt⟩⟩),
                    hGt_ne, hbtw₀, hlev₀⟩
          msgs_card_le_one := fun h1 => by omega
          msgs_budget := fun h2 => by
            intro L_max
            have hL₂_le : F₂.level ≤ L_max := level_le_log_of_inv hinv h₂
            have hL₁_lt : F₁.level < L_max := lt_of_lt_of_le hlt hL₂_le
            have hsum_er2 := sum_erase2 h₁ h₂ hne (fragRemBudget L_max)
            have hsum_ins := Finset.sum_insert hnotMem (f := fragRemBudget L_max)
            have hucard : F₂'.verts.card = F₂.verts.card + F₁.verts.card :=
              Finset.card_union_of_disjoint hdisj₁₂.symm
            have hb_F₂' : fragRemBudget L_max F₂' =
                fragRemBudget L_max F₂ +
                  perVertexBudget L_max F₂.level F₂.phase * F₁.verts.card := by
              simp only [F₂', fragRemBudget, hucard, Nat.left_distrib]
            have hpv_le : perVertexBudget L_max F₂.level F₂.phase + 1 ≤
                perVertexBudget L_max F₁.level F₁.phase := by
              rw [hph₁]
              simp only [perVertexBudget, hL₁_lt, ↓reduceIte]
              cases hph₂ : F₂.phase with
              | sleeping | halted => rw [hph₂] at hok₂; cases hok₂
              | searching =>
                dsimp only
                omega
              | found e₂ =>
                dsimp only
                split_ifs <;> omega
            have hmul_le : (perVertexBudget L_max F₂.level F₂.phase + 1) * F₁.verts.card ≤
                fragRemBudget L_max F₁ := by
              simpa only [fragRemBudget] using Nat.mul_le_mul_right F₁.verts.card hpv_le
            rw [Nat.right_distrib, one_mul] at hmul_le
            have htot : ({ s.msgs with initiate := s.msgs.initiate + F₁.verts.card } :
                MsgCount).total = s.msgs.total + F₁.verts.card := by
              simp only [MsgCount.total]; omega
            have hprev := hinv.msgs_budget h2
            dsimp only [L_max, F₂'] at *
            omega }
  | merge F₁ F₂ e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨h₁, h₂, hne, hlev_eq, hph₁, hph₂, hbtw⟩ := hg
    injection htr with hs'
    subst hs'
    let F' : Fragment V := ⟨F₁.verts ∪ F₂.verts, F₁.level + 1, some e, .searching⟩
    obtain ⟨hnotMem, hnemp, hdisj, hcov⟩ := combine_partition hinv h₁ h₂ (Fcomb := F') rfl
    obtain ⟨_, hmoe₁⟩ := hinv.found_isMOE F₁ h₁ e hph₁
    have he_fin : e ∈ G.edgeFinset := mem_edgeFinset.mpr hmoe₁.1.1
    obtain ⟨he_not_br, he_not_rej, hbr_int, hrej_int, hbr_card⟩ :=
      combine_edge_facts hinv h₁ h₂ hne (Fcomb := F') rfl hbtw
    have hdisj₁₂ : Disjoint F₁.verts F₂.verts := hinv.verts_disjoint F₁ h₁ F₂ h₂ hne
    have hpow_F' : 2 ^ F'.level ≤ F'.verts.card := by
      have hp₁ := hinv.two_pow_level_le F₁ h₁
      have hp₂ := hinv.two_pow_level_le F₂ h₂
      rw [← hlev_eq] at hp₂
      have huc : F'.verts.card = F₁.verts.card + F₂.verts.card :=
        Finset.card_union_of_disjoint hdisj₁₂
      change 2 ^ (F₁.level + 1) ≤ F'.verts.card
      rw [Nat.pow_succ, huc]
      omega
    have hL₁_succ_le : F₁.level + 1 ≤ Nat.log 2 (Fintype.card V) := by
      have hle_V : 2 ^ (F₁.level + 1) ≤ Fintype.card V :=
        hpow_F'.trans (Finset.card_le_univ _)
      exact Nat.le_log_of_pow_le (by decide) hle_V
    have hcard2 : 2 ≤ Fintype.card V := by
      have h2_le : 2 ≤ 2 ^ (F₁.level + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (F₁.level + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact h2_le.trans (hpow_F'.trans (Finset.card_le_univ _))
    refine
      { verts_nonempty := hnemp
        verts_disjoint := hdisj
        verts_cover := hcov
        branch_sub := Finset.insert_subset he_fin hinv.branch_sub
        rejected_sub := hinv.rejected_sub
        branch_rejected_disjoint :=
          Finset.disjoint_insert_left.mpr ⟨he_not_rej, hinv.branch_rejected_disjoint⟩
        branch_isMOE := fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz_old
          · exact ⟨F₁.verts, hmoe₁⟩
          · exact hinv.branch_isMOE z hz_old
        branch_internal := hbr_int
        rejected_internal := hrej_int
        frag_branch_card := hbr_card
        two_pow_level_le := fun G₀ hG₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · exact hpow_F'
          · exact hinv.two_pow_level_le G₀
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er))
        sleeping_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.sleeping_spec G₀
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
        searching_level_pos := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · exact Nat.succ_pos _
          · exact hinv.searching_level_pos G₀
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
        halted_spec := fun G₀ hG₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · obtain ⟨hu, hsub⟩ := hinv.halted_spec G₀
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) hph₀
            exact ⟨hu, hsub.trans (Finset.union_subset_union_left (Finset.subset_insert _ _))⟩
        found_isMOE := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · exact hinv.found_isMOE G₀
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h_er)) e₀ hph₀
        found_target_level := fun G₀ hG₀ e₀ hph₀ => by
          rcases Finset.mem_insert.mp hG₀ with rfl | h_er
          · cases hph₀
          · obtain ⟨hne₀₂, h_er₁⟩ := Finset.mem_erase.mp h_er
            obtain ⟨hne₀₁, hG₀_in⟩ := Finset.mem_erase.mp h_er₁
            obtain ⟨Gt, hGt, hGt_ne, hbtw₀, hlev₀⟩ := hinv.found_target_level G₀ hG₀_in e₀ hph₀
            obtain ⟨ua, hua, ub, hub, he₀_eq⟩ := (betweenSets_eq_true_iff _ _ _).mp hbtw₀
            have hF'_ne_G₀ : F' ≠ G₀ := fun h => hnotMem (h ▸ h_er)
            by_cases hGt₁ : Gt = F₁
            · subst hGt₁
              refine ⟨F', Finset.mem_insert_self _ _, hF'_ne_G₀, ?_, ?_⟩
              · rw [betweenSets_eq_true_iff]
                exact ⟨ua, hua, ub, Finset.mem_union_left _ hub, he₀_eq⟩
              · dsimp only [F']; omega
            · by_cases hGt₂ : Gt = F₂
              · subst hGt₂
                refine ⟨F', Finset.mem_insert_self _ _, hF'_ne_G₀, ?_, ?_⟩
                · rw [betweenSets_eq_true_iff]
                  exact ⟨ua, hua, ub, Finset.mem_union_right _ hub, he₀_eq⟩
                · dsimp only [F']; omega
              · exact ⟨Gt, Finset.mem_insert_of_mem
                  (Finset.mem_erase.mpr ⟨hGt₂, Finset.mem_erase.mpr ⟨hGt₁, hGt⟩⟩),
                  hGt_ne, hbtw₀, hlev₀⟩
        msgs_card_le_one := fun h1 => by omega
        msgs_budget := fun h2 => by
          intro L_max
          have hL₁_lt : F₁.level < L_max := hL₁_succ_le
          have hsum_er2 := sum_erase2 h₁ h₂ hne (fragRemBudget L_max)
          have hsum_ins := Finset.sum_insert hnotMem (f := fragRemBudget L_max)
          have hucard : F'.verts.card = F₁.verts.card + F₂.verts.card :=
            Finset.card_union_of_disjoint hdisj₁₂
          have hb_F' : fragRemBudget L_max F' + F₁.verts.card + F₂.verts.card =
              fragRemBudget L_max F₁ + fragRemBudget L_max F₂ := by
            simp only [F', fragRemBudget, hph₁, hph₂, perVertexBudget, ← hlev_eq, hL₁_lt,
              ↓reduceIte, hucard]
            have h1 : 5 * (L_max - 1 - F₁.level) + 2 = 5 * (L_max - (F₁.level + 1)) + 1 + 1 := by
              omega
            rw [h1, ← Nat.left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.right_distrib,
              one_mul]
            omega
          have htot : ({ s.msgs with
              initiate := s.msgs.initiate + F₁.verts.card + F₂.verts.card } : MsgCount).total =
              s.msgs.total + F₁.verts.card + F₂.verts.card := by
            simp only [MsgCount.total]; omega
          have hprev := hinv.msgs_budget h2
          dsimp only [L_max, F'] at *
          omega }

private theorem fragInv_mTr {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s₀ s : FragState V}
    {as : List (FragAction V)} (hmtr : (fragLTS G w).MTr s₀ as s) :
    FragInv G w s₀ → FragInv G w s := by
  induction hmtr with
  | refl => exact id
  | stepL htr _ ih => exact fun hinv => ih (fragInv_step hinv htr)

private theorem FragReachable.inv {V W : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hr : FragReachable G w s) : FragInv G w s := by
  obtain ⟨as, has⟩ := hr
  exact fragInv_mTr has (fragInv_init V G w)

/-! ### MST subtree invariant, fragment trees, and chord rejection -/

private theorem FragInv.edgeSet_branchGraph {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W} {s : FragState V}
    (hinv : FragInv G w s) :
    s.branchGraph.edgeSet = (s.branchEdges : Set (Sym2 V)) := by
  rw [FragState.branchGraph, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left,
    Set.disjoint_left]
  intro e he hdiag
  have heG : e ∈ G.edgeSet := mem_edgeFinset.mp (hinv.branch_sub he)
  exact G.not_isDiag_of_mem_edgeSet heG (Sym2.mem_diagSet.mp hdiag)

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §§2–3,
pp. 68–72; modeling atomic fragment-level phases rather than Appendix per-node FIFO message
queues): at every reachable `FragState`, `s.branchGraph` is a subgraph of every MST of `(G, w)`
when edge weights are injective on `G.edgeSet`. -/
theorem FragReachable.branchGraph_le_of_isMST {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G T : SimpleGraph V} [DecidableRel G.Adj] {w : Sym2 V → W}
    (hinj : Set.InjOn w G.edgeSet) {s : FragState V} (hr : FragReachable G w s)
    (hMST : IsMST G w T) :
    s.branchGraph ≤ T := by
  have hinv := hr.inv
  refine le_of_forall_isMOE_of_isMST_of_injOn hinj (fun e he => ?_) hMST
  rw [hinv.edgeSet_branchGraph, Finset.mem_coe] at he
  exact hinv.branch_isMOE e he

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §§2–3,
pp. 68–72): on a finite connected graph with injective edge weights, `s.branchGraph` is acyclic at
every reachable `FragState`. -/
theorem FragReachable.branchGraph_isAcyclic {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) :
    s.branchGraph.IsAcyclic := by
  have hinv := hr.inv
  refine isAcyclic_of_forall_isMOE_of_injOn hconn hinj fun e he => ?_
  rw [hinv.edgeSet_branchGraph, Finset.mem_coe] at he
  exact hinv.branch_isMOE e he

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, pp. 69–72):
at every reachable `FragState` on a connected graph with injective edge weights, every fragment
`F ∈ s.fragments` induces a connected tree in `s.branchGraph`. -/
theorem FragReachable.fragment_induce_isTree {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) {F : Fragment V} (hF : F ∈ s.fragments) :
    (s.branchGraph.induce (F.verts : Set V)).IsTree := by
  classical
  have hinv := hr.inv
  let H := s.branchGraph.induce (F.verts : Set V)
  have hacyc : H.IsAcyclic := (hr.branchGraph_isAcyclic hconn hinj).induce (F.verts : Set V)
  have himg : H.edgeFinset.image (Sym2.map Subtype.val) =
      s.branchEdges.filter fun z => bothIn F.verts z = true := by
    ext z
    simp only [Finset.mem_image, mem_edgeFinset, Finset.mem_filter]
    constructor
    · rintro ⟨e, heH, rfl⟩
      induction e using Sym2.ind with
      | _ x y =>
        have hadj_br : s.branchGraph.Adj x.1 y.1 := H.mem_edgeSet.mp heH
        have hz_mem : s(x.1, y.1) ∈ s.branchGraph.edgeSet := s.branchGraph.mem_edgeSet.mpr hadj_br
        rw [hinv.edgeSet_branchGraph, Finset.mem_coe] at hz_mem
        refine ⟨hz_mem, ?_⟩
        change bothIn F.verts s(x.1, y.1) = true
        rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨Finset.mem_coe.mp x.2, Finset.mem_coe.mp y.2⟩
    · rintro ⟨hzB, hzIn⟩
      induction z using Sym2.ind with
      | _ a b =>
        rw [bothIn_mk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hzIn
        have hz_set : s(a, b) ∈ s.branchGraph.edgeSet := by
          rw [hinv.edgeSet_branchGraph, Finset.mem_coe]; exact hzB
        have hadj_br : s.branchGraph.Adj a b := s.branchGraph.mem_edgeSet.mp hz_set
        refine ⟨s(⟨a, Finset.mem_coe.mpr hzIn.1⟩, ⟨b, Finset.mem_coe.mpr hzIn.2⟩), ?_, rfl⟩
        exact H.mem_edgeSet.mpr hadj_br
  let S : Set V := F.verts
  have hinj_map : Function.Injective (Sym2.map (Subtype.val : S → V)) :=
    Sym2.map.injective Subtype.val_injective
  have hcard_edges : H.edgeFinset.card =
      (s.branchEdges.filter fun z => bothIn F.verts z = true).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj_map]
  have hcard_verts : Fintype.card (F.verts : Set V) = F.verts.card := Fintype.card_coe F.verts
  have hcard_eq : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← H.coe_edgeFinset, Set.ncard_coe_finset]
  rw [isTree_iff_isAcyclic_and_ncard_edgeSet_add_one_eq_card, Nat.card_eq_fintype_card,
    hcard_eq, hcard_edges, hcard_verts]
  exact ⟨hacyc, hinv.frag_branch_card F hF⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, p. 71):
every `Rejected` edge belongs to `G` and has both endpoints inside a single fragment. -/
theorem FragReachable.rejected_internal_chord {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hr : FragReachable G w s) {e : Sym2 V} (he : e ∈ s.rejectedEdges) :
    e ∈ G.edgeSet ∧ ∃ F ∈ s.fragments, ∀ x ∈ e, x ∈ F.verts := by
  have hinv := hr.inv
  obtain ⟨F, hF, hboth⟩ := hinv.rejected_internal e he
  exact ⟨mem_edgeFinset.mp (hinv.rejected_sub he), F, hF, (bothIn_eq_true_iff F.verts e).mp hboth⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, p. 71):
on a finite connected graph with injective edge weights, no `Rejected` edge belongs to any MST of
`(G, w)`. -/
theorem FragReachable.rejected_notMem_isMST {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G T : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) (hMST : IsMST G w T) {e : Sym2 V} (he : e ∈ s.rejectedEdges) :
    e ∉ T.edgeSet := by
  have hinv := hr.inv
  obtain ⟨_, F, hF, hboth⟩ := hr.rejected_internal_chord he
  have htree := hr.fragment_induce_isTree hconn hinj hF
  have hbr_le_T : s.branchGraph ≤ T := hr.branchGraph_le_of_isMST hinj hMST
  have he_not_br : e ∉ s.branchEdges :=
    Finset.disjoint_right.mp hinv.branch_rejected_disjoint he
  induction e using Sym2.ind with
  | _ u v =>
    intro heT
    have hu : u ∈ F.verts := hboth u (Sym2.mem_mk_left u v)
    have hv : v ∈ F.verts := hboth v (Sym2.mem_mk_right u v)
    obtain ⟨p_ind⟩ := htree.connected ⟨u, Finset.mem_coe.mpr hu⟩ ⟨v, Finset.mem_coe.mpr hv⟩
    let p_br : s.branchGraph.Walk u v := p_ind.map (SimpleGraph.Embedding.induce _).toHom
    let p_T : T.Walk u v := p_br.mapLe hbr_le_T
    have hnot_edges : s(u, v) ∉ p_T.edges := by
      intro hm
      have hm_br : s(u, v) ∈ s.branchGraph.edgeSet := by
        rw [Walk.edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at hm
        exact p_br.edges_subset_edgeSet hm
      rw [hinv.edgeSet_branchGraph, Finset.mem_coe] at hm_br
      exact he_not_br hm_br
    have hbridge : T.IsBridge s(u, v) := isAcyclic_iff_forall_isBridge.mp hMST.1.2.isAcyclic heT
    exact hnot_edges (isBridge_iff_forall_walk_mem_edges.mp hbridge p_T)

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, p. 71):
on a finite connected graph with injective edge weights, no `Rejected` edge is ever a cut-MOE across
any cut `S : Finset V`. -/
theorem FragReachable.rejected_not_isMOE {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) {e : Sym2 V} (he : e ∈ s.rejectedEdges) (S : Finset V) :
    ¬ IsMOE G w S e := by
  intro hmoe
  obtain ⟨T, hMST⟩ := exists_isMST hconn w
  exact hr.rejected_notMem_isMST hconn hinj hMST he (hmoe.mem_edgeSet_of_isMST_of_injOn hinj hMST)

/-! ### Exponential fragment size and logarithmic level bound -/

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, p. 72):
every reachable fragment at level `L` contains at least `2 ^ L` vertices. -/
theorem FragReachable.two_pow_level_le_card {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hr : FragReachable G w s) {F : Fragment V} (hF : F ∈ s.fragments) :
    2 ^ F.level ≤ F.verts.card :=
  hr.inv.two_pow_level_le F hF

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, p. 72):
every reachable fragment has level at most `Nat.log 2 (Fintype.card V)`. -/
theorem FragReachable.level_le_log_card {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hr : FragReachable G w s) {F : Fragment V} (hF : F ∈ s.fragments) :
    F.level ≤ Nat.log 2 (Fintype.card V) :=
  level_le_log_of_inv hr.inv hF

/-! ### Deadlock-freedom and minimum-level smallest-MOE progress -/

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, pp. 72–73):
under injective edge weights, whenever every fragment of minimum level `L_min` is in phase `found`
(and at least one fragment has level `L_min`), some minimum-level fragment has an enabled `absorb`
or mutual `merge` transition in `fragLTS G w` (no waiting cycle can occur). -/
theorem FragReachable.exists_absorb_or_merge_of_minLevel_found {V W : Type*} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W]
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) {L_min : ℕ} (hex_min : ∃ F ∈ s.fragments, F.level = L_min)
    (hle_min : ∀ F ∈ s.fragments, L_min ≤ F.level)
    (hfound_min : ∀ F ∈ s.fragments, F.level = L_min → ∃ e, F.phase = .found e) :
    ∃ a s', a.isCombine = true ∧ (fragLTS G w).Tr s a s' := by
  have hinv := hr.inv
  obtain ⟨F₀, hF₀, hF₀_lev⟩ := hex_min
  obtain ⟨e_def, _⟩ := hfound_min F₀ hF₀ hF₀_lev
  let moeEdge : Fragment V → Sym2 V := fun F =>
    match F.phase with
    | .found e => e
    | _ => e_def
  let minFrags := s.fragments.filter fun F => F.level = L_min
  have hmin_ne : minFrags.Nonempty := ⟨F₀, Finset.mem_filter.mpr ⟨hF₀, hF₀_lev⟩⟩
  obtain ⟨F₁, hF₁_min, hF₁_wt⟩ := Finset.exists_min_image minFrags (fun F => w (moeEdge F)) hmin_ne
  obtain ⟨h₁, h₁_lev⟩ := Finset.mem_filter.mp hF₁_min
  obtain ⟨e₁, hph₁⟩ := hfound_min F₁ h₁ h₁_lev
  obtain ⟨_, hmoe₁⟩ := hinv.found_isMOE F₁ h₁ e₁ hph₁
  obtain ⟨F₂, h₂, h₂_ne_₁, hbtw, hlev₁₂⟩ := hinv.found_target_level F₁ h₁ e₁ hph₁
  have h₁_ne_₂ : F₁ ≠ F₂ := h₂_ne_₁.symm
  have hF₂_not_sleep : F₂.phase ≠ .sleeping := by
    intro hsleep
    obtain ⟨v, rfl⟩ := hinv.sleeping_spec F₂ h₂ hsleep
    have hL₀ : L_min = 0 := le_antisymm (hle_min _ h₂) (Nat.zero_le _)
    obtain ⟨_, hph_c⟩ := hfound_min _ h₂ hL₀.symm
    cases hph_c
  have hF₂_not_halt : F₂.phase ≠ .halted := by
    intro hhalt
    obtain ⟨huniv, _⟩ := hinv.halted_spec F₂ h₂ hhalt
    obtain ⟨u₁, hu₁⟩ := hinv.verts_nonempty F₁ h₁
    have hu₁_₂ : u₁ ∈ F₂.verts := huniv.symm ▸ Finset.mem_univ u₁
    exact Finset.disjoint_left.mp (hinv.verts_disjoint F₁ h₁ F₂ h₂ h₁_ne_₂) hu₁ hu₁_₂
  have hok₂ : (match F₂.phase with
      | .searching | .found _ => true
      | .sleeping | .halted => false) = true := by
    cases hp : F₂.phase with
    | sleeping => exact absurd hp hF₂_not_sleep
    | halted => exact absurd hp hF₂_not_halt
    | searching | found _ => rfl
  rcases lt_or_eq_of_le (h₁_lev ▸ hlev₁₂) with hlt | heq_lev
  · have hstep : (fragStep? G w s (.absorb F₁ F₂)).isSome := by
      dsimp only [fragStep?]
      rw [hph₁]
      dsimp only
      split_ifs with hc
      · rfl
      · exact absurd ⟨h₁, h₂, h₁_ne_₂, h₁_lev ▸ hlt, hok₂, hbtw⟩ hc
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
    exact ⟨.absorb F₁ F₂, s', rfl, hs'⟩
  · have h₂_lev : F₂.level = L_min := heq_lev.symm
    obtain ⟨e₂, hph₂⟩ := hfound_min F₂ h₂ h₂_lev
    obtain ⟨_, hmoe₂⟩ := hinv.found_isMOE F₂ h₂ e₂ hph₂
    have hF₂_min : F₂ ∈ minFrags := Finset.mem_filter.mpr ⟨h₂, h₂_lev⟩
    have hw_1_le_2 : w e₁ ≤ w e₂ := by
      have h := hF₁_wt F₂ hF₂_min
      simpa only [moeEdge, hph₁, hph₂] using h
    obtain ⟨u₁, hu₁, v₁, hv₁, he₁_eq⟩ := (betweenSets_eq_true_iff _ _ _).mp hbtw
    have hu₁_not₂ : u₁ ∉ F₂.verts :=
      Finset.disjoint_left.mp (hinv.verts_disjoint F₁ h₁ F₂ h₂ h₁_ne_₂) hu₁
    have hout_e₁_from₂ : IsOutgoingEdge G F₂.verts e₁ :=
      ⟨hmoe₁.1.1, v₁, hv₁, u₁, hu₁_not₂, he₁_eq.trans Sym2.eq_swap⟩
    have hw_2_le_1 : w e₂ ≤ w e₁ := hmoe₂.2 e₁ hout_e₁_from₂
    have he_eq : e₁ = e₂ :=
      hinj hmoe₁.1.1 hmoe₂.1.1 (le_antisymm hw_1_le_2 hw_2_le_1)
    subst he_eq
    have hstep : (fragStep? G w s (.merge F₁ F₂ e₁)).isSome := by
      dsimp only [fragStep?]
      split_ifs with hc
      · rfl
      · exact absurd ⟨h₁, h₂, h₁_ne_₂, h₁_lev.trans h₂_lev.symm, hph₁, hph₂, hbtw⟩ hc
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
    exact ⟨.merge F₁ F₂ e₁, s', rfl, hs'⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, pp. 72–73):
on a finite connected graph with injective edge weights, every non-halted reachable `FragState` has
at least one enabled transition in `fragLTS G w`. -/
theorem FragReachable.exists_step_of_not_halted {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) [LinearOrder W]
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) (hnot : ¬ s.Halted) :
    ∃ a s', (fragLTS G w).Tr s a s' := by
  have hinv := hr.inv
  obtain ⟨v_any⟩ := hconn.nonempty
  by_cases hex_sleep : ∃ F ∈ s.fragments, F.phase = .sleeping
  · obtain ⟨F, hF, hsleep⟩ := hex_sleep
    obtain ⟨v, rfl⟩ := hinv.sleeping_spec F hF hsleep
    by_cases huniv : ({v} : Finset V) = Finset.univ
    · have hstep : (fragStep? G w s (.wakeupSingleton v)).isSome := by
        dsimp only [fragStep?]
        split_ifs with hc
        · rfl
        · exact absurd ⟨hF, huniv⟩ hc
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
      exact ⟨.wakeupSingleton v, s', hs'⟩
    · obtain ⟨e, hmoe⟩ := exists_isMOE hconn w (Finset.singleton_nonempty v) huniv
      have hstep : (fragStep? G w s (.wakeup v e)).isSome := by
        dsimp only [fragStep?]
        split_ifs with hc
        · rfl
        · exact absurd ⟨hF, hmoe⟩ hc
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
      exact ⟨.wakeup v e, s', hs'⟩
  · push Not at hex_sleep
    obtain ⟨F_any, hF_any, _⟩ := hinv.verts_cover v_any
    have hfrags_ne : s.fragments.Nonempty := ⟨F_any, hF_any⟩
    obtain ⟨F_min, hF_min, hmin_le⟩ :=
      Finset.exists_min_image s.fragments Fragment.level hfrags_ne
    let L_min := F_min.level
    by_cases hex_search : ∃ F ∈ s.fragments, F.level = L_min ∧ F.phase = .searching
    · obtain ⟨F, hF, hF_lev, hsearch⟩ := hex_search
      by_cases huniv : F.verts = Finset.univ
      · by_cases hnoBasic : noBasicInternalEdges G s F.verts = true
        · have hstep : (fragStep? G w s (.haltSearch F)).isSome := by
            dsimp only [fragStep?]
            split_ifs with hc
            · rfl
            · exact absurd ⟨hF, hsearch, huniv, hnoBasic⟩ hc
          obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
          exact ⟨.haltSearch F, s', hs'⟩
        · have hnotB : ¬ (∀ c ∈ G.edgeFinset, bothIn F.verts c = true → s.edgeState c ≠ .basic) :=
            fun hall => hnoBasic ((noBasicInternalEdges_eq_true_iff G s F.verts).mpr hall)
          push Not at hnotB
          obtain ⟨c, hc, hboth, hbas⟩ := hnotB
          have _ : F ∈ s.fragments ∧ F.phase = .searching ∧ c ∈ G.edgeFinset ∧
              bothIn F.verts c = true ∧ s.edgeState c = .basic :=
            ⟨hF, hsearch, hc, hboth, hbas⟩
          have hstep : (fragStep? G w s (.rejectChord F c false)).isSome := by
            dsimp only [fragStep?]
            split_ifs <;> rfl
          obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
          exact ⟨.rejectChord F c false, s', hs'⟩
      · obtain ⟨e, hmoe⟩ := exists_isMOE hconn w (hinv.verts_nonempty F hF) huniv
        have hallAcc : allNodeMOEsAccepted G w s F = true := by
          unfold allNodeMOEsAccepted
          refine decide_eq_true fun u _ v _ _ _ => ?_
          obtain ⟨Ft, hFt, hv_Ft⟩ := hinv.verts_cover v
          exact ⟨Ft, hFt, hv_Ft, hF_lev ▸ hmin_le Ft hFt⟩
        have hstep : (fragStep? G w s (.completeSearch F e)).isSome := by
          dsimp only [fragStep?]
          split_ifs with hc
          · rfl
          · exact absurd ⟨hF, hsearch, huniv, hmoe, hallAcc⟩ hc
        obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hstep
        exact ⟨.completeSearch F e, s', hs'⟩
    · push Not at hex_search
      have hfound_min : ∀ F ∈ s.fragments, F.level = L_min → ∃ e, F.phase = .found e := by
        intro F hF hlev
        cases hp : F.phase with
        | sleeping => exact absurd hp (hex_sleep F hF)
        | searching => exact absurd hp (hex_search F hF hlev)
        | halted => exact absurd ⟨F, hF, hp⟩ hnot
        | found e => exact ⟨e, rfl⟩
      obtain ⟨a, s', _, htr⟩ := hr.exists_absorb_or_merge_of_minLevel_found hinj
        ⟨F_min, hF_min, rfl⟩ hmin_le hfound_min
      exact ⟨a, s', htr⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, pp. 72–73):
a reachable `FragState` is terminal in `fragLTS G w` if and only if `s.Halted` holds. -/
theorem FragReachable.isTerminal_iff_halted {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) [LinearOrder W]
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) :
    (fragLTS G w).IsTerminal s ↔ s.Halted := by
  constructor
  · intro hterm
    by_contra hnot
    obtain ⟨a, s', htr⟩ := hr.exists_step_of_not_halted hconn hinj hnot
    exact hterm a s' htr
  · rintro ⟨Fh, hFh, hph_h⟩ a s' htr
    have hinv := hr.inv
    obtain ⟨huniv, hall_class⟩ := hinv.halted_spec Fh hFh hph_h
    have honly : ∀ F ∈ s.fragments, F = Fh := by
      intro F hF
      by_contra hne
      obtain ⟨u, hu⟩ := hinv.verts_nonempty F hF
      have hu_Fh : u ∈ Fh.verts := huniv.symm ▸ Finset.mem_univ u
      exact Finset.disjoint_left.mp (hinv.verts_disjoint F hF Fh hFh hne) hu hu_Fh
    change fragStep? G w s a = some s' at htr
    cases a with
    | wakeupSingleton v =>
      simp only [fragStep?] at htr
      split_ifs at htr with hg
      have heq := honly _ hg.1
      rw [← heq] at hph_h; cases hph_h
    | wakeup v e =>
      simp only [fragStep?] at htr
      split_ifs at htr with hg
      have heq := honly _ hg.1
      rw [← heq] at hph_h; cases hph_h
    | rejectChord F e dual =>
      dsimp only [fragStep?] at htr
      by_cases hg : F ∈ s.fragments ∧ F.phase = .searching ∧ e ∈ G.edgeFinset ∧
          bothIn F.verts e = true ∧ s.edgeState e = .basic
      · have heq := honly F hg.1
        rw [heq, hph_h] at hg; cases hg.2.1
      · simp only [hg] at htr; cases htr
    | completeSearch F e =>
      simp only [fragStep?] at htr
      split_ifs at htr with hg
      have heq := honly F hg.1
      rw [heq, hph_h] at hg; cases hg.2.1
    | haltSearch F =>
      simp only [fragStep?] at htr
      split_ifs at htr with hg
      have heq := honly F hg.1
      rw [heq, hph_h] at hg; cases hg.2.1
    | absorb F₁ F₂ =>
      dsimp only [fragStep?] at htr
      cases hp : F₁.phase with
      | sleeping | searching | halted => rw [hp] at htr; cases htr
      | found e =>
        rw [hp] at htr
        dsimp only at htr
        split_ifs at htr with hg
        exact hg.2.2.1 ((honly F₁ hg.1).trans (honly F₂ hg.2.1).symm)
    | merge F₁ F₂ e =>
      simp only [fragStep?] at htr
      split_ifs at htr with hg
      exact hg.2.2.1 ((honly F₁ hg.1).trans (honly F₂ hg.2.1).symm)

/-! ### Exact MST termination, combine-step bound, and `5 N log₂ N + 2 E` message complexity -/

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §§2–3,
pp. 68–73): at every halted reachable `FragState`, `s.branchGraph` is the unique minimum-weight
spanning tree of `(G, w)` and `s.rejectedEdges = G.edgeFinset \ s.branchEdges`. -/
theorem FragReachable.halted_branchGraph_isMST {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) (hhalt : s.Halted) :
    IsMST G w s.branchGraph ∧ s.rejectedEdges = G.edgeFinset \ s.branchEdges := by
  have hinv := hr.inv
  obtain ⟨Fh, hFh, hph_h⟩ := hhalt
  obtain ⟨huniv, hall_class⟩ := hinv.halted_spec Fh hFh hph_h
  have htree_ind := hr.fragment_induce_isTree hconn hinj hFh
  have hconn_br : s.branchGraph.Connected := by
    have : Nonempty V := hconn.nonempty
    refine Connected.mk fun u v => ?_
    have hu : u ∈ Fh.verts := huniv.symm ▸ Finset.mem_univ u
    have hv : v ∈ Fh.verts := huniv.symm ▸ Finset.mem_univ v
    obtain ⟨p⟩ := htree_ind.connected ⟨u, Finset.mem_coe.mpr hu⟩ ⟨v, Finset.mem_coe.mpr hv⟩
    exact ⟨p.map (SimpleGraph.Embedding.induce _).toHom⟩
  have hMST_br : IsMST G w s.branchGraph := by
    refine isMST_of_forall_isMOE_of_connected_of_injOn hconn hinj hconn_br fun e he => ?_
    rw [hinv.edgeSet_branchGraph, Finset.mem_coe] at he
    exact hinv.branch_isMOE e he
  have hrej_eq : s.rejectedEdges = G.edgeFinset \ s.branchEdges := by
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · intro he
      exact ⟨hinv.rejected_sub he,
        Finset.disjoint_right.mp hinv.branch_rejected_disjoint he⟩
    · rintro ⟨heG, he_not_br⟩
      rcases Finset.mem_union.mp (hall_class heG) with hbr | hrej
      · exact absurd hbr he_not_br
      · exact hrej
  exact ⟨hMST_br, hrej_eq⟩

private def phaseRank {V : Type*} : FragPhase V → ℕ
  | .sleeping => 3
  | .searching => 2
  | .found _ => 1
  | .halted => 0

/-- Progress measure strictly decreasing across every `fragLTS` transition. -/
private def stepMeasure {V : Type*} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (s : FragState V) : ℕ :=
  3 * s.fragments.card + (∑ F ∈ s.fragments, phaseRank F.phase) +
    (G.edgeFinset \ (s.branchEdges ∪ s.rejectedEdges)).card

private theorem stepMeasure_replace_phase {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hinv : FragInv G w s) {F F' : Fragment V} (hF : F ∈ s.fragments)
    (hverts : F'.verts = F.verts) (hlevel : F'.level = F.level)
    (hrank : phaseRank F'.phase < phaseRank F.phase) (msgs' : MsgCount) :
    let s' : FragState V := { s with fragments := insert F' (s.fragments.erase F), msgs := msgs' }
    stepMeasure G s' < stepMeasure G s ∧ s'.fragments.card = s.fragments.card := by
  obtain ⟨hnotMem, _⟩ := replace_phase_partition hinv hF hverts hlevel
  have hcard_er := Finset.card_erase_add_one hF
  have hcard_ins := Finset.card_insert_of_notMem hnotMem
  have hsum_er := Finset.sum_erase_add s.fragments (fun G₀ => phaseRank G₀.phase) hF
  have hsum_ins := Finset.sum_insert hnotMem (f := fun G₀ => phaseRank G₀.phase)
  dsimp only [stepMeasure]
  omega

private theorem stepMeasure_combine {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hinv : FragInv G w s) {F₁ F₂ Fcomb : Fragment V}
    (h₁ : F₁ ∈ s.fragments) (h₂ : F₂ ∈ s.fragments) (hne : F₁ ≠ F₂)
    (hverts : Fcomb.verts = F₁.verts ∪ F₂.verts)
    (hrank : phaseRank Fcomb.phase < 3 + phaseRank F₁.phase + phaseRank F₂.phase)
    (e : Sym2 V) (msgs' : MsgCount) :
    let s' : FragState V :=
      { s with
        fragments := insert Fcomb ((s.fragments.erase F₁).erase F₂)
        branchEdges := insert e s.branchEdges
        msgs := msgs' }
    stepMeasure G s' < stepMeasure G s ∧ s'.fragments.card + 1 = s.fragments.card := by
  obtain ⟨hnotMem, _⟩ := combine_partition hinv h₁ h₂ hverts
  have h₂_er : F₂ ∈ s.fragments.erase F₁ := Finset.mem_erase.mpr ⟨hne.symm, h₂⟩
  have hc1 := Finset.card_erase_add_one h₁
  have hc2 := Finset.card_erase_add_one h₂_er
  have hc3 := Finset.card_insert_of_notMem hnotMem
  have hsum_er2 := sum_erase2 h₁ h₂ hne (fun G₀ => phaseRank G₀.phase)
  have hsum_ins := Finset.sum_insert hnotMem (f := fun G₀ => phaseRank G₀.phase)
  have hsdiff_le : (G.edgeFinset \ (insert e s.branchEdges ∪ s.rejectedEdges)).card ≤
      (G.edgeFinset \ (s.branchEdges ∪ s.rejectedEdges)).card :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
      (Finset.union_subset_union_left (Finset.subset_insert _ _)))
  dsimp only [stepMeasure]
  omega

private theorem stepMeasure_lt_of_step {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s s' : FragState V} {a : FragAction V} (hinv : FragInv G w s)
    (htr : fragStep? G w s a = some s') :
    stepMeasure G s' < stepMeasure G s ∧
      s'.fragments.card + (if a.isCombine then 1 else 0) = s.fragments.card := by
  cases a with
  | wakeupSingleton v =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    injection htr with hs'; subst hs'
    simpa only [FragAction.isCombine, Bool.false_eq_true, ↓reduceIte, add_zero] using
      stepMeasure_replace_phase hinv hg.1 (F' := ⟨{v}, 0, none, .halted⟩) rfl rfl
        (Nat.zero_lt_succ 2) s.msgs
  | wakeup v e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    injection htr with hs'; subst hs'
    simpa only [FragAction.isCombine, Bool.false_eq_true, ↓reduceIte, add_zero] using
      stepMeasure_replace_phase hinv hg.1 (F' := ⟨{v}, 0, none, .found e⟩) rfl rfl
        (Nat.lt_succ_of_le (Nat.le_succ 1)) _
  | rejectChord F e dual =>
    dsimp only [fragStep?] at htr
    by_cases hg : F ∈ s.fragments ∧ F.phase = .searching ∧ e ∈ G.edgeFinset ∧
        bothIn F.verts e = true ∧ s.edgeState e = .basic
    · simp only [hg] at htr
      obtain ⟨_, _, he_fin, _, hbasic⟩ := hg
      injection htr with hs'; subst hs'
      have he_not_br : e ∉ s.branchEdges := by
        intro hm; simp only [FragState.edgeState, hm, ↓reduceIte, reduceCtorEq] at hbasic
      have he_not_rej : e ∉ s.rejectedEdges := by
        intro hm
        simp only [FragState.edgeState, he_not_br, hm, ↓reduceIte, reduceCtorEq] at hbasic
      have he_sdiff : e ∈ G.edgeFinset \ (s.branchEdges ∪ s.rejectedEdges) := by
        rw [Finset.mem_sdiff, Finset.mem_union, not_or]
        exact ⟨he_fin, he_not_br, he_not_rej⟩
      have hsdiff_eq : G.edgeFinset \ (s.branchEdges ∪ insert e s.rejectedEdges) =
          (G.edgeFinset \ (s.branchEdges ∪ s.rejectedEdges)).erase e := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        tauto
      have hcard_sd : (G.edgeFinset \ (s.branchEdges ∪ insert e s.rejectedEdges)).card + 1 =
          (G.edgeFinset \ (s.branchEdges ∪ s.rejectedEdges)).card := by
        rw [hsdiff_eq, Finset.card_erase_add_one he_sdiff]
      refine ⟨?_, rfl⟩
      dsimp only [stepMeasure]
      rw [← hcard_sd]
      exact Nat.add_lt_add_left (Nat.lt_succ_self _) _
    · simp only [hg] at htr; cases htr
  | completeSearch F e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    injection htr with hs'; subst hs'
    have hrank : phaseRank (FragPhase.found e) < phaseRank F.phase := by
      rw [hg.2.1]; exact Nat.lt_succ_self 1
    simpa only [FragAction.isCombine, Bool.false_eq_true, ↓reduceIte, add_zero] using
      stepMeasure_replace_phase hinv hg.1 (F' := { F with phase := .found e }) rfl rfl hrank _
  | haltSearch F =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    injection htr with hs'; subst hs'
    have hrank : phaseRank (FragPhase.halted : FragPhase V) < phaseRank F.phase := by
      rw [hg.2.1]; exact Nat.zero_lt_succ 1
    simpa only [FragAction.isCombine, Bool.false_eq_true, ↓reduceIte, add_zero] using
      stepMeasure_replace_phase hinv hg.1 (F' := { F with phase := .halted }) rfl rfl hrank _
  | absorb F₁ F₂ =>
    dsimp only [fragStep?] at htr
    cases hp : F₁.phase with
    | sleeping | searching | halted => rw [hp] at htr; cases htr
    | found e =>
      rw [hp] at htr
      dsimp only at htr
      split_ifs at htr with hg
      obtain ⟨h₁, h₂, hne, _, _, _⟩ := hg
      injection htr with hs'; subst hs'
      have hrank : phaseRank F₂.phase < 3 + phaseRank F₁.phase + phaseRank F₂.phase := by
        have hr₁ : phaseRank F₁.phase = 1 := by rw [hp]; rfl
        omega
      simpa only [FragAction.isCombine, ↓reduceIte] using
        stepMeasure_combine hinv h₁ h₂ hne
          (Fcomb := ⟨F₂.verts ∪ F₁.verts, F₂.level, F₂.core, F₂.phase⟩)
          (Finset.union_comm _ _) hrank e _
  | merge F₁ F₂ e =>
    simp only [fragStep?] at htr
    split_ifs at htr with hg
    obtain ⟨h₁, h₂, hne, _, hp₁, hp₂, _⟩ := hg
    injection htr with hs'; subst hs'
    have hrank : phaseRank (FragPhase.searching : FragPhase V) <
        3 + phaseRank F₁.phase + phaseRank F₂.phase := by
      rw [hp₁, hp₂]
      exact Nat.lt_succ_of_le (Nat.le_add_left 2 2)
    simpa only [FragAction.isCombine, ↓reduceIte] using
      stepMeasure_combine hinv h₁ h₂ hne
        (Fcomb := ⟨F₁.verts ∪ F₂.verts, F₁.level + 1, some e, .searching⟩) rfl hrank e _

private theorem mTr_card_and_measure {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s s' : FragState V} {as : List (FragAction V)}
    (hinv : FragInv G w s) (hmtr : (fragLTS G w).MTr s as s') :
    s'.fragments.card + (as.filter FragAction.isCombine).length = s.fragments.card ∧
      as.length + stepMeasure G s' ≤ stepMeasure G s := by
  induction hmtr with
  | refl =>
    simp only [List.filter_nil, List.length_nil, add_zero, zero_add, le_rfl, and_self]
  | @stepL s₁ a s₂ as s₃ htr _ ih =>
    have hinv₂ := fragInv_step hinv htr
    obtain ⟨hm_lt, hc_eq⟩ := stepMeasure_lt_of_step hinv htr
    obtain ⟨ih_c, ih_m⟩ := ih hinv₂
    constructor
    · cases hc : a.isCombine <;> simp only [List.filter_cons, hc, ↓reduceIte, Bool.false_eq_true,
        List.length_cons] <;> simp only [hc, ↓reduceIte, Bool.false_eq_true] at hc_eq <;> omega
    · simp only [List.length_cons]; omega

private theorem initFragState_fragments_card (V : Type*) [Fintype V] [DecidableEq V] :
    (initFragState V).fragments.card = Fintype.card V := by
  simp only [initFragState]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_univ
  · intro u _ v _ huv
    exact Finset.singleton_injective (congrArg Fragment.verts huv)

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §§2–3,
pp. 68–73): every finite execution trace from `initFragState V` performs at most
`Fintype.card V - 1` fragment-combining (`absorb` or `merge`) steps (when `Nonempty V`, and `0`
when `IsEmpty V`). -/
theorem fragLTS_combineSteps_le {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [LinearOrder W] (w : Sym2 V → W)
    {as : List (FragAction V)} {s : FragState V}
    (hmtr : (fragLTS G w).MTr (initFragState V) as s) :
    (as.filter FragAction.isCombine).length ≤ Fintype.card V - 1 := by
  obtain ⟨hc, _⟩ := mTr_card_and_measure (fragInv_init V G w) hmtr
  rw [initFragState_fragments_card] at hc
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · omega
  · have ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hpos
    have hr : FragReachable G w s := ⟨as, hmtr⟩
    obtain ⟨F₀, hF₀, _⟩ := hr.inv.verts_cover v₀
    have hpos_f : 1 ≤ s.fragments.card := Finset.card_pos.mpr ⟨F₀, hF₀⟩
    omega

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §§2–3,
pp. 68–73): every complete execution trace (`μs ∈ (fragLTS G w).completeTraces (initFragState V)`)
on a finite connected graph with injective edge weights reaches a halted state whose `branchGraph`
is the unique MST of `(G, w)` after **exact** `Fintype.card V - 1` combine steps. -/
theorem fragLTS_completeTrace_combineSteps_eq {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet)
    {as : List (FragAction V)} (hcomp : as ∈ (fragLTS G w).completeTraces (initFragState V)) :
    ∃ s, (fragLTS G w).MTr (initFragState V) as s ∧ s.Halted ∧ IsMST G w s.branchGraph ∧
      (as.filter FragAction.isCombine).length = Fintype.card V - 1 := by
  obtain ⟨s, hterm, hmtr⟩ := hcomp
  have hr : FragReachable G w s := ⟨as, hmtr⟩
  have hhalt : s.Halted := (hr.isTerminal_iff_halted hconn hinj).mp hterm
  have hhalt' := hhalt
  obtain ⟨hMST, _⟩ := hr.halted_branchGraph_isMST hconn hinj hhalt
  obtain ⟨hc, _⟩ := mTr_card_and_measure (fragInv_init V G w) hmtr
  rw [initFragState_fragments_card] at hc
  obtain ⟨Fh, hFh, hph_h⟩ := hhalt
  obtain ⟨huniv, _⟩ := hr.inv.halted_spec Fh hFh hph_h
  have hs_one : s.fragments = {Fh} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hFh, fun F hF => ?_⟩
    by_contra hne
    obtain ⟨u, hu⟩ := hr.inv.verts_nonempty F hF
    have hu_Fh : u ∈ Fh.verts := huniv.symm ▸ Finset.mem_univ u
    exact Finset.disjoint_left.mp (hr.inv.verts_disjoint F hF Fh hFh hne) hu hu_Fh
  have hcard1 : s.fragments.card = 1 := by rw [hs_one, Finset.card_singleton]
  exact ⟨s, hmtr, hhalt', hMST, by omega⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §3, pp. 72–73):
from every reachable `FragState` on a finite connected graph with injective edge weights, a
multi-step execution reaches a halted state whose `branchGraph` is the unique MST of `(G, w)`. -/
theorem FragReachable.exists_mTr_halted {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) :
    ∃ as s', (fragLTS G w).MTr s as s' ∧ s'.Halted ∧ IsMST G w s'.branchGraph := by
  suffices ∀ m (s : FragState V), stepMeasure G s ≤ m → FragReachable G w s →
      ∃ as s', (fragLTS G w).MTr s as s' ∧ s'.Halted ∧ IsMST G w s'.branchGraph by
    exact this (stepMeasure G s) s le_rfl hr
  intro m
  induction m with
  | zero =>
    intro s hm hr
    by_cases hhalt : s.Halted
    · exact ⟨[], s, .refl, hhalt, (hr.halted_branchGraph_isMST hconn hinj hhalt).1⟩
    · obtain ⟨a, s', htr⟩ := hr.exists_step_of_not_halted hconn hinj hhalt
      obtain ⟨hlt, _⟩ := stepMeasure_lt_of_step hr.inv htr
      omega
  | succ m ih =>
    intro s hm hr
    by_cases hhalt : s.Halted
    · exact ⟨[], s, .refl, hhalt, (hr.halted_branchGraph_isMST hconn hinj hhalt).1⟩
    · obtain ⟨a, s₁, htr⟩ := hr.exists_step_of_not_halted hconn hinj hhalt
      obtain ⟨hlt, _⟩ := stepMeasure_lt_of_step hr.inv htr
      obtain ⟨as, s', hmtr, hh', hMST'⟩ := ih s₁ (by omega) (hr.step htr)
      exact ⟨a :: as, s', .stepL htr hmtr, hh', hMST'⟩

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §4, p. 73;
counting the seven message types of `fragStep?`): at every reachable `FragState` (including
termination), total messages exchanged satisfy
`s.msgs.total ≤ 5 * Fintype.card V * Nat.log 2 (Fintype.card V) + 2 * G.edgeFinset.card`. -/
theorem FragReachable.msgs_total_le {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [LinearOrder W] {w : Sym2 V → W}
    {s : FragState V} (hr : FragReachable G w s) :
    s.msgs.total ≤ 5 * Fintype.card V * Nat.log 2 (Fintype.card V) + 2 * G.edgeFinset.card := by
  have hinv := hr.inv
  rcases le_or_gt (Fintype.card V) 1 with h1 | h2
  · rw [hinv.msgs_card_le_one h1]
    exact Nat.zero_le _
  · have h2' : 2 ≤ Fintype.card V := h2
    have hL_pos : 1 ≤ Nat.log 2 (Fintype.card V) :=
      Nat.le_log_of_pow_le (by decide) (by simpa using h2')
    have hbud := hinv.msgs_budget h2'
    dsimp only at hbud
    have hcoeff : (5 * (Nat.log 2 (Fintype.card V) - 1) + 3) * Fintype.card V ≤
        5 * Fintype.card V * Nat.log 2 (Fintype.card V) := by
      have hle_c : 5 * (Nat.log 2 (Fintype.card V) - 1) + 3 ≤
          5 * Nat.log 2 (Fintype.card V) := by omega
      calc (5 * (Nat.log 2 (Fintype.card V) - 1) + 3) * Fintype.card V
          ≤ (5 * Nat.log 2 (Fintype.card V)) * Fintype.card V :=
            Nat.mul_le_mul_right _ hle_c
        _ = 5 * Fintype.card V * Nat.log 2 (Fintype.card V) := by
            rw [Nat.mul_right_comm]
    omega

/-- Fragment-phase protocol step toward `#7508` (after [GallagerHumbletSpira1983], §4, p. 73;
sharpened halted-state message bound for `2 ≤ Fintype.card V`, tight at `s.msgs.total = 6` on
`K₂`): `s.msgs.total + 4 * Fintype.card V ≤ 5 * Fintype.card V * Nat.log 2 (Fintype.card V) +`
`2 * G.edgeFinset.card + 2`. -/
theorem FragReachable.halted_msgs_total_add_four_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [AddCancelCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    {w : Sym2 V → W} (hinj : Set.InjOn w G.edgeSet) {s : FragState V}
    (hr : FragReachable G w s) (hhalt : s.Halted) (h2 : 2 ≤ Fintype.card V) :
    s.msgs.total + 4 * Fintype.card V ≤
      5 * Fintype.card V * Nat.log 2 (Fintype.card V) + 2 * G.edgeFinset.card + 2 := by
  have hinv := hr.inv
  obtain ⟨hMST, _⟩ := hr.halted_branchGraph_isMST hconn hinj hhalt
  have hbr_sdiff : s.branchEdges ⊆ G.edgeFinset \ s.rejectedEdges := by
    intro e he
    exact Finset.mem_sdiff.mpr
      ⟨hinv.branch_sub he, Finset.disjoint_left.mp hinv.branch_rejected_disjoint he⟩
  have hbr_le_unrej : s.branchEdges.card ≤ (G.edgeFinset \ s.rejectedEdges).card :=
    Finset.card_le_card hbr_sdiff
  have hbr_card_tree : s.branchEdges.card + 1 = Fintype.card V := by
    have h1 := hMST.1.2.card_edgeFinset
    have h2_eq : s.branchGraph.edgeFinset = s.branchEdges := by
      ext e
      rw [mem_edgeFinset, hinv.edgeSet_branchGraph, Finset.mem_coe]
    rwa [h2_eq] at h1
  have hL_pos : 1 ≤ Nat.log 2 (Fintype.card V) :=
    Nat.le_log_of_pow_le (by decide) (by simpa using h2)
  have hbud := hinv.msgs_budget h2
  dsimp only at hbud
  have hcoeff : (5 * (Nat.log 2 (Fintype.card V) - 1) + 3) * Fintype.card V +
      2 * Fintype.card V = 5 * Fintype.card V * Nat.log 2 (Fintype.card V) := by
    have hsub : 5 * (Nat.log 2 (Fintype.card V) - 1) + 3 + 2 =
        5 * Nat.log 2 (Fintype.card V) := by omega
    calc (5 * (Nat.log 2 (Fintype.card V) - 1) + 3) * Fintype.card V + 2 * Fintype.card V
        = (5 * (Nat.log 2 (Fintype.card V) - 1) + 3 + 2) * Fintype.card V := by
            rw [← Nat.right_distrib]
      _ = (5 * Nat.log 2 (Fintype.card V)) * Fintype.card V := by rw [hsub]
      _ = 5 * Fintype.card V * Nat.log 2 (Fintype.card V) := by rw [Nat.mul_right_comm]
  omega

end Cslib.Distributed.MinimumSpanningTree
