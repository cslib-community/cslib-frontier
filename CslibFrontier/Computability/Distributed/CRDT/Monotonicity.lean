/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.CRDT.DataTypes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max

/-!
# Semilattice Irrevocable-Emission Coordination-Free Consistency ↔ Monotonicity

This module formalizes a **semilattice irrevocable-emission and monotone-observation model** step
toward #7502 for coordination-free distributed query evaluation over partitionable `CvRDT`
semilattices (motivated by Hellerstein's *CALM Conjecture* [Hellerstein2010], §4.1 Conjecture 1,
and the relational-transducer characterization of Ameloot, Neven, and Van den Bussche
[AmelootNevenVandenBussche2011], §§2.1, 3–6, Proposition 11, Theorem 12, and Corollary 13).

In a partitionable asynchronous `CvRDT` network over finite replica set `P` and state semilattice
`S` (`[SemilatticeSup S]`):

* **Coordination-free local emission:** before waiting for cross-replica coordination, each replica
  `p : P` evaluates an output query `emit : S → Finset Fact` locally against its own partitioned
  state `cfg p : S` and accumulates emitted facts irrevocably (`emitted p ∪ emit s'`) across
  arbitrary asynchronous gossip merges `(src, dst)` (`runGossipEmit`).
* **Split-brain retraction safety (`SemilatticeCoordinationFreeConsistent P emit`):** across all
  initial partitioned replica configurations `cfg : P → S` and all finite gossip schedules `hops`,
  every fact irrevocably emitted at any replica belongs to the globally converged query output
  `emit (globalMergedState cfg)`.

## Main theorems in the semilattice model

1. **Exact Semilattice `iff` Characterization
   (`semilatticeCoordinationFreeConsistent_iff_monotone`):**
   Over any multi-replica network (`[Nontrivial P]`, i.e. at least two distinct replicas), an
   irrevocable fact-emission query `emit : S → Finset Fact` is coordination-free consistent if and
   only if `Monotone emit` holds on the state semilattice `S` (using the two-replica split-brain
   horizontal partition construction of [AmelootNevenVandenBussche2011], §6, proof of Theorem 12).
   Moreover, when `Monotone emit` holds, any all-pairs gossip schedule brings every replica's
   accumulated irrevocable output to the exact global answer `emit (globalMergedState cfg)`
   (`emitted_eq_global_of_monotone`), whereas on a 1-node network (`[Subsingleton P]`)
   every query trivially avoids cross-replica retraction
   (`semilatticeCoordinationFreeConsistent_of_subsingleton`, matching
   [AmelootNevenVandenBussche2011], §4 Example 2).
2. **Preorder-Valued Observable Queries (`semilatticeObservableConsistent_iff_monotone`):**
   Generalizes the characterization to arbitrary `[Preorder Out]` local observations `q : S → Out`
   (`SemilatticeObservableConsistent P q ↔ Monotone q` under `[Nontrivial P]`).
3. **Positive Monotone CRDT Queries:**
   Threshold queries on `GCounter` (`gcounterThresholdEmit`, `gcounterThresholdBool`) and
   membership / monotone selection-projection queries on `GSet` (`gsetMemEmit`, `gsetFilterImage`)
   are proved coordination-free consistent.
4. **Negative Non-Monotone CRDT Queries (Split-Brain Retraction Refutations):**
   Set emptiness (`gsetIsEmptyEmit`, [AmelootNevenVandenBussche2011], §5 Example 10), negation /
   tombstone set difference (`TwoPhaseSet.elements`), and exact count (`gcounterExactCountEmit k`)
   all fail monotonicity and are refuted as coordination-free consistent over any `[Nontrivial P]`.

## Model scope relative to primary sources

This module models local query evaluation `emit : S → Finset Fact` and `q : S → Out` over abstract
`SemilatticeSup S` replica states and gossip merges rather than the full relational transducer
networks `(N, Π)` over database schemas `(S_in, S_sys, S_msg, S_mem)` with `Id`/`All` system
relations, network-topology independence, obliviousness equivalence, and syntactic Datalog /
`FO`+`while` / Dedalus characterizations of [AmelootNevenVandenBussche2011] (§§2–8, Theorems 6, 12,
16, 18 & Corollaries 13, 14, 17). Those database-transducer and query-language characterizations
remain open under #7502.

## Main definitions

* `Cslib.Distributed.CRDT.globalMergedState`: global semilattice supremum across all replicas `P`.
* `Cslib.Distributed.CRDT.IrrevocableReplicaState`,
  `Cslib.Distributed.CRDT.initIrrevocableState`,
  `Cslib.Distributed.CRDT.gossipEmitStep`,
  `Cslib.Distributed.CRDT.runGossipEmit`: asynchronous gossip execution with irrevocable local fact
  emission.
* `Cslib.Distributed.CRDT.SemilatticeCoordinationFreeConsistent`: split-brain retraction freedom for
  irrevocable `Finset Fact` emission over `P`.
* `Cslib.Distributed.CRDT.gossipReplicaStates`,
  `Cslib.Distributed.CRDT.SemilatticeObservableConsistent`: preorder-enriched local observation
  consistency across gossip schedules.
* `Cslib.Distributed.CRDT.gcounterThresholdEmit`,
  `Cslib.Distributed.CRDT.gcounterThresholdBool`,
  `Cslib.Distributed.CRDT.gsetMemEmit`,
  `Cslib.Distributed.CRDT.gsetFilterImage`: positive monotone CRDT queries.
* `Cslib.Distributed.CRDT.gsetIsEmptyEmit`,
  `Cslib.Distributed.CRDT.gcounterExactCountEmit`: negative non-monotone emptiness and exact-count
  queries.

## Main results

* `Monotone.semilatticeCoordinationFreeConsistent` and
  `Cslib.Distributed.CRDT.semilatticeCoordinationFreeConsistent_iff_monotone`: monotonicity implies
  `SemilatticeCoordinationFreeConsistent P emit` over `[Nonempty P]`, and is equivalent to it over
  `[Nontrivial P]`.
* `Cslib.Distributed.CRDT.emitted_eq_global_of_monotone`: under `Monotone emit`, any all-pairs
  gossip schedule converges every replica's irrevocable output to `emit (globalMergedState cfg)`.
* `Cslib.Distributed.CRDT.semilatticeCoordinationFreeConsistent_of_subsingleton`: on
  `[Subsingleton P]`, `SemilatticeCoordinationFreeConsistent P emit` holds unconditionally, showing
  `[Nontrivial P]` is necessary.
* `Monotone.semilatticeObservableConsistent` and
  `Cslib.Distributed.CRDT.semilatticeObservableConsistent_iff_monotone`: monotonicity implies
  `SemilatticeObservableConsistent P q` over `[Nonempty P]`, and is equivalent to it over
  `[Nontrivial P]`.
* `Cslib.Distributed.CRDT.semilatticeCoordinationFreeConsistent_gcounterThreshold`,
  `Cslib.Distributed.CRDT.semilatticeObservableConsistent_gcounterThresholdBool`,
  `Cslib.Distributed.CRDT.semilatticeCoordinationFreeConsistent_gsetMem`, and
  `Cslib.Distributed.CRDT.semilatticeCoordinationFreeConsistent_gsetFilterImage`: positive monotone
  query instantiations.
* `Cslib.Distributed.CRDT.not_semilatticeCoordinationFreeConsistent_gsetIsEmpty`,
  `Cslib.Distributed.CRDT.not_semilatticeCoordinationFreeConsistent_twoPhaseSetElements`, and
  `Cslib.Distributed.CRDT.not_semilatticeCoordinationFreeConsistent_gcounterExactCount`: split-brain
  impossibility instantiations for emptiness, set difference / negation, and exact count.

## References

* [J. M. Hellerstein, *The Declarative Imperative: Experiences and Conjectures in Distributed
  Logic*][Hellerstein2010]
* [T. J. Ameloot, F. Neven, J. Van den Bussche, *Relational transducers for declarative
  networking*][AmelootNevenVandenBussche2011]
-/

public section

namespace Cslib.Distributed.CRDT

/-! ### Semilattice Irrevocable-Emission Gossip Model -/

/-- Globally converged semilattice state `⨆ p : P, cfg p` across all replicas `p : P`. -/
@[expose]
def globalMergedState {P S : Type*} [Fintype P] [Nonempty P] [SemilatticeSup S]
    (cfg : P → S) : S :=
  Finset.univ.sup' Finset.univ_nonempty cfg

/-- Replica states resulting from folding asynchronous `(· ⊔ ·)` gossip merges `hops` from `cfg`. -/
@[expose]
def gossipReplicaStates {P S : Type*} [DecidableEq P] [SemilatticeSup S]
    (cfg : P → S) (hops : List (P × P)) : P → S :=
  hops.foldl (fun rep (src, dst) => Function.update rep dst (rep dst ⊔ rep src)) cfg

private theorem gossipReplicaStates_le_of_forall_le {P S : Type*} [DecidableEq P] [SemilatticeSup S]
    (cfg : P → S) (hops : List (P × P)) {u : S} (h : ∀ p, cfg p ≤ u) :
    ∀ p, gossipReplicaStates cfg hops p ≤ u := by
  induction hops generalizing cfg with
  | nil => exact h
  | cons hop tl ih =>
    obtain ⟨src, dst⟩ := hop
    refine ih (Function.update cfg dst (cfg dst ⊔ cfg src)) fun p => ?_
    by_cases hpd : p = dst
    · subst hpd; simp [sup_le (h p) (h src)]
    · simp [Function.update_of_ne hpd, h p]

/-- Distributed state of replicas running a semilattice `CvRDT` alongside an irrevocable output
accumulator `emitted : P → Finset Fact` (modeling append-only transition outputs
`out(ρ) = ⋃_n out(τ_n)` as in [AmelootNevenVandenBussche2011], §2.1 & §3, pp. 3–4). -/
@[ext]
structure IrrevocableReplicaState (P S Fact : Type*) where
  /-- Current local semilattice state at each replica. -/
  replica : P → S
  /-- Cumulative set of facts irrevocably emitted at each replica so far. -/
  emitted : P → Finset Fact

/-- Initial coordination-free configuration: before any cross-replica messages are exchanged, each
replica `p` evaluates and emits `emit (cfg p)` purely from its own local state `cfg p`. -/
@[expose]
def initIrrevocableState {P S Fact : Type*} (emit : S → Finset Fact) (cfg : P → S) :
    IrrevocableReplicaState P S Fact where
  replica := cfg
  emitted p := emit (cfg p)

/-- One asynchronous gossip-and-emit step along directed pair `hop = (src, dst)`: `dst` merges
`src`'s state via `(· ⊔ ·)` and irrevocably appends `emit` evaluated at its updated state. -/
@[expose]
def gossipEmitStep {P S Fact : Type*} [DecidableEq P] [SemilatticeSup S] [DecidableEq Fact]
    (emit : S → Finset Fact) (st : IrrevocableReplicaState P S Fact) (hop : P × P) :
    IrrevocableReplicaState P S Fact :=
  let (src, dst) := hop
  let s' := st.replica dst ⊔ st.replica src
  { replica := Function.update st.replica dst s'
    emitted := Function.update st.emitted dst (st.emitted dst ∪ emit s') }

/-- Execute a finite schedule `hops : List (P × P)` of asynchronous gossip merges starting from
`initIrrevocableState emit cfg`. -/
@[expose]
def runGossipEmit {P S Fact : Type*} [DecidableEq P] [SemilatticeSup S] [DecidableEq Fact]
    (emit : S → Finset Fact) (cfg : P → S) (hops : List (P × P)) :
    IrrevocableReplicaState P S Fact :=
  hops.foldl (gossipEmitStep emit) (initIrrevocableState emit cfg)

/-- Coordination-free consistency in the semilattice irrevocable-emission model (step toward
#7502, motivated by [Hellerstein2010], §4.1 Conjecture 1, and [AmelootNevenVandenBussche2011],
§§4–5): across all partitioned initial assignments `cfg : P → S` and all asynchronous gossip
schedules `hops`, no replica ever irrevocably emits a split-brain fact outside the globally
converged answer `emit (globalMergedState cfg)`. -/
@[expose]
def SemilatticeCoordinationFreeConsistent (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {S Fact : Type*} [SemilatticeSup S] [DecidableEq Fact] (emit : S → Finset Fact) : Prop :=
  ∀ (cfg : P → S) (hops : List (P × P)) (p : P),
    (runGossipEmit emit cfg hops).emitted p ⊆ emit (globalMergedState cfg)

/-- The split-brain configuration (`p₁` holds `s₁ ≤ s₂`, every other replica holds `s₂`) merges
to `s₂`. -/
private theorem globalMergedState_splitBrain {P S : Type*} [Fintype P] [DecidableEq P]
    [Nonempty P] [SemilatticeSup S] {p₁ p₂ : P} (hp : p₁ ≠ p₂) {s₁ s₂ : S} (hs : s₁ ≤ s₂) :
    globalMergedState (fun q => if q = p₁ then s₁ else s₂) = s₂ :=
  le_antisymm (Finset.sup'_le _ _ fun q _ => by split_ifs; exacts [hs, le_rfl])
    (by simpa [globalMergedState, hp.symm] using
      Finset.le_sup' (fun q => if q = p₁ then s₁ else s₂) (Finset.mem_univ p₂))

section IrrevocableCharacterization

variable {P S Fact : Type*} [Fintype P] [DecidableEq P] [SemilatticeSup S] [DecidableEq Fact]

omit [Fintype P] in
private theorem foldl_gossipEmitStep_replica (emit : S → Finset Fact)
    (st : IrrevocableReplicaState P S Fact) (hops : List (P × P)) :
    (hops.foldl (gossipEmitStep emit) st).replica = gossipReplicaStates st.replica hops := by
  induction hops generalizing st with
  | nil => rfl
  | cons hop tl ih => exact ih (gossipEmitStep emit st hop)

omit [Fintype P] in
private theorem foldl_gossipEmitStep_le_bound (emit : S → Finset Fact)
    (st : IrrevocableReplicaState P S Fact) (hops : List (P × P)) (u : S)
    (hrep : ∀ p, st.replica p ≤ u) :
    ∀ p, (hops.foldl (gossipEmitStep emit) st).replica p ≤ u := by
  rw [foldl_gossipEmitStep_replica]
  exact gossipReplicaStates_le_of_forall_le st.replica hops hrep

omit [Fintype P] in
private theorem foldl_gossipEmitStep_mono (emit : S → Finset Fact)
    (st : IrrevocableReplicaState P S Fact) (hops : List (P × P)) :
    (∀ p, st.replica p ≤ (hops.foldl (gossipEmitStep emit) st).replica p) ∧
      (∀ p, st.emitted p ⊆ (hops.foldl (gossipEmitStep emit) st).emitted p) := by
  induction hops generalizing st with
  | nil => exact ⟨fun _ => le_rfl, fun _ => Finset.Subset.refl _⟩
  | cons hop tl ih =>
    obtain ⟨src, dst⟩ := hop
    obtain ⟨ih_rep, ih_em⟩ := ih (gossipEmitStep emit st (src, dst))
    refine ⟨fun p => le_trans ?_ (ih_rep p), fun p => Finset.Subset.trans ?_ (ih_em p)⟩
    · rcases eq_or_ne p dst with rfl | hpd <;> simp [gossipEmitStep, *, le_sup_left]
    · rcases eq_or_ne p dst with rfl | hpd <;> simp [gossipEmitStep, *]

omit [Fintype P] in
private theorem foldl_gossipEmitStep_emitted_sub_of_monotone {emit : S → Finset Fact}
    (hmono : Monotone emit) (st : IrrevocableReplicaState P S Fact)
    (hops : List (P × P)) (u : S)
    (hrep : ∀ p, st.replica p ≤ u)
    (hem : ∀ p, st.emitted p ⊆ emit u) :
    ∀ p, (hops.foldl (gossipEmitStep emit) st).emitted p ⊆ emit u := by
  induction hops generalizing st with
  | nil => exact hem
  | cons hop tl ih =>
    obtain ⟨src, dst⟩ := hop
    refine ih (gossipEmitStep emit st (src, dst)) (fun p => ?_) fun p => ?_
    · rcases eq_or_ne p dst with rfl | hpd <;>
        simp [gossipEmitStep, *, sup_le (hrep _) (hrep _), hrep p]
    · rcases eq_or_ne p dst with rfl | hpd
      · simpa [gossipEmitStep] using Finset.union_subset (hem _) (hmono (sup_le (hrep _) (hrep _)))
      · simp [gossipEmitStep, Function.update_of_ne hpd, hem p]

/-- Every monotone query `emit : S → Finset Fact` is coordination-free consistent over any
nonempty finite replica set `P`. -/
theorem _root_.Monotone.semilatticeCoordinationFreeConsistent [Nonempty P]
    {emit : S → Finset Fact} (hmono : Monotone emit) :
    SemilatticeCoordinationFreeConsistent P emit := fun cfg hops p =>
  foldl_gossipEmitStep_emitted_sub_of_monotone hmono
    (initIrrevocableState emit cfg) hops (globalMergedState cfg)
    (fun q => Finset.le_sup' cfg (Finset.mem_univ q))
    (fun q => hmono (Finset.le_sup' cfg (Finset.mem_univ q)))
    p

/-- Semilattice irrevocable-emission coordination-free consistency characterization step (toward
#7502, adapting the split-brain horizontal-partition argument of [AmelootNevenVandenBussche2011],
§6 Theorem 12 & Corollary 13, p. 8, to `SemilatticeSup S` states, motivated by [Hellerstein2010],
§4.1 Conjecture 1): over any finite network `P` with at least two distinct replicas
(`[Nontrivial P]`), `SemilatticeCoordinationFreeConsistent P emit` holds if and only if
`Monotone emit`. -/
theorem semilatticeCoordinationFreeConsistent_iff_monotone [Nontrivial P]
    {emit : S → Finset Fact} :
    SemilatticeCoordinationFreeConsistent P emit ↔ Monotone emit := by
  constructor
  · intro hcfc s₁ s₂ hs f hf
    obtain ⟨p₁, p₂, hp₁₂⟩ := exists_pair_ne P
    -- Split-brain partition: `p₁` holds `s₁` while every peer `q ≠ p₁` (including `p₂`) holds `s₂`.
    have hsub := hcfc (fun q => if q = p₁ then s₁ else s₂) [] p₁
    rw [globalMergedState_splitBrain hp₁₂ hs] at hsub
    exact hsub (by simpa [runGossipEmit, initIrrevocableState] using hf)
  · exact Monotone.semilatticeCoordinationFreeConsistent

omit [Fintype P] in
private theorem foldl_hops_achieves_pairs (emit : S → Finset Fact)
    (st : IrrevocableReplicaState P S Fact) (hops : List (P × P)) :
    ∀ src dst, (src, dst) ∈ hops →
      st.replica src ≤ (hops.foldl (gossipEmitStep emit) st).replica dst := by
  induction hops generalizing st with
  | nil => intro _ _ h; cases h
  | cons hd tl ih =>
    obtain ⟨u, v⟩ := hd
    intro src dst hmem
    let st₁ := gossipEmitStep emit st (u, v)
    obtain ⟨hmono_tl, _⟩ := foldl_gossipEmitStep_mono emit st₁ tl
    rcases List.mem_cons.mp hmem with hhd | htl
    · rcases Prod.mk.inj hhd with ⟨rfl, rfl⟩
      have huv : st.replica src ≤ st₁.replica dst := by
        simp [st₁, gossipEmitStep, le_sup_right]
      exact le_trans huv (hmono_tl dst)
    · have hu_le : st.replica src ≤ st₁.replica src :=
        (foldl_gossipEmitStep_mono emit st [(u, v)]).1 src
      exact le_trans hu_le (ih st₁ src dst htl)

/-- Under `Monotone emit`, any gossip schedule `hops` that covers every ordered pair `(src, dst)`
(`∀ src dst, (src, dst) ∈ hops`) converges every replica `p`'s state to `globalMergedState cfg` and
its cumulative irrevocable output to the exact global answer `emit (globalMergedState cfg)`. -/
theorem emitted_eq_global_of_monotone [Nonempty P] {emit : S → Finset Fact}
    (hmono : Monotone emit) (cfg : P → S) {hops : List (P × P)}
    (hcovers : ∀ src dst : P, (src, dst) ∈ hops) (p : P) :
    (runGossipEmit emit cfg hops).replica p = globalMergedState cfg ∧
      (runGossipEmit emit cfg hops).emitted p =
        emit (globalMergedState cfg) := by
  have hrep_eq : ∀ dst : P,
      (runGossipEmit emit cfg hops).replica dst = globalMergedState cfg := by
    intro dst
    apply le_antisymm
    · exact foldl_gossipEmitStep_le_bound emit (initIrrevocableState emit cfg)
        hops (globalMergedState cfg)
        (fun q => Finset.le_sup' cfg (Finset.mem_univ q)) dst
    · rw [globalMergedState, Finset.sup'_le_iff]
      intro src _
      exact foldl_hops_achieves_pairs emit (initIrrevocableState emit cfg)
        hops src dst (hcovers src dst)
  refine ⟨hrep_eq p, Finset.Subset.antisymm ?_ ?_⟩
  · exact foldl_gossipEmitStep_emitted_sub_of_monotone hmono
      (initIrrevocableState emit cfg) hops (globalMergedState cfg)
      (fun q => Finset.le_sup' cfg (Finset.mem_univ q))
      (fun q => hmono (Finset.le_sup' cfg (Finset.mem_univ q))) p
  · have hlast : ∀ (l : List (P × P)) (st : IrrevocableReplicaState P S Fact),
        (∃ src, (src, p) ∈ l) →
        emit ((l.foldl (gossipEmitStep emit) st).replica p) ⊆
          (l.foldl (gossipEmitStep emit) st).emitted p := by
      intro l
      induction l using List.reverseRecOn with
      | nil => rintro _ ⟨_, ⟨⟩⟩
      | append_singleton initH hop ih =>
        rintro st ⟨s₀, hs₀⟩
        obtain ⟨src, dst⟩ := hop
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        by_cases hdp : dst = p
        · subst hdp
          simp only [gossipEmitStep, Function.update_self]
          exact Finset.subset_union_right
        · simp only [gossipEmitStep, Function.update_of_ne (Ne.symm hdp)]
          exact ih st ⟨s₀, (List.mem_append.mp hs₀).resolve_right fun h =>
            hdp (Prod.mk.inj (List.mem_singleton.mp h)).2.symm⟩
    rw [← hrep_eq p]
    exact hlast hops (initIrrevocableState emit cfg) ⟨p, hcovers p p⟩

/-- Single-replica degeneracy step (toward #7502, after [AmelootNevenVandenBussche2011], §4
Example 2, p. 5): on a 1-replica network (`[Subsingleton P]`),
`SemilatticeCoordinationFreeConsistent P emit` holds for every `emit` (even non-monotone ones),
confirming that `[Nontrivial P]` (`2 ≤ |P|`) in `semilatticeCoordinationFreeConsistent_iff_monotone`
is necessary. -/
theorem semilatticeCoordinationFreeConsistent_of_subsingleton [Nonempty P] [Subsingleton P]
    (emit : S → Finset Fact) :
    SemilatticeCoordinationFreeConsistent P emit := by
  intro cfg hops p
  have hcfg_const : ∀ q, cfg q = cfg p := fun q => congrArg cfg (Subsingleton.elim q p)
  have hglob : globalMergedState cfg = cfg p := by
    apply le_antisymm
    · rw [globalMergedState, Finset.sup'_le_iff]
      exact fun q _ => (hcfg_const q).le
    · exact Finset.le_sup' cfg (Finset.mem_univ p)
  have hinv : ∀ (l : List (P × P)) (st : IrrevocableReplicaState P S Fact),
      (∀ q, st.replica q = cfg p) → (∀ q, st.emitted q = emit (cfg p)) →
      ∀ q, (l.foldl (gossipEmitStep emit) st).emitted q = emit (cfg p) := by
    intro l
    induction l with
    | nil => exact fun _ _ hem q => hem q
    | cons hop tl ih =>
      intro st hrep hem
      obtain ⟨src, dst⟩ := hop
      refine ih (gossipEmitStep emit st (src, dst)) (fun q => ?_) (fun q => ?_) <;>
        simp [gossipEmitStep, Function.update_apply, hrep, hem]
  have hem_eq : (runGossipEmit emit cfg hops).emitted p = emit (cfg p) :=
    hinv hops (initIrrevocableState emit cfg) hcfg_const
      (fun q => congrArg emit (hcfg_const q)) p
  rw [hem_eq, hglob]

end IrrevocableCharacterization

/-! ### Preorder-Valued Observable Queries (`q : S → Out`) -/

/-- Semilattice observable-query consistency over `[Preorder Out]`: at every point along any
asynchronous gossip schedule `hops` from any partitioned configuration `cfg : P → S`, every
replica's local observation `q (state p)` is bounded above in `Out` by the globally converged
answer `q (globalMergedState cfg)` (for instance, on `Bool` with `false ≤ true`, once a local
predicate becomes `true` it never flips back to `false` upon merging remote partitions). -/
@[expose]
def SemilatticeObservableConsistent (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {S Out : Type*} [SemilatticeSup S] [Preorder Out] (q : S → Out) : Prop :=
  ∀ (cfg : P → S) (hops : List (P × P)) (p : P),
    q (gossipReplicaStates cfg hops p) ≤ q (globalMergedState cfg)

/-- Every monotone observation `q : S → Out` is observable-consistent over any nonempty finite
replica set `P`. -/
theorem _root_.Monotone.semilatticeObservableConsistent {P S Out : Type*}
    [Fintype P] [DecidableEq P] [Nonempty P] [SemilatticeSup S] [Preorder Out]
    {q : S → Out} (hmono : Monotone q) :
    SemilatticeObservableConsistent P q := fun cfg hops p =>
  hmono (gossipReplicaStates_le_of_forall_le cfg hops
    (fun r => Finset.le_sup' cfg (Finset.mem_univ r)) p)

/-- Semilattice observable-query consistency characterization step (toward #7502): over any finite
network `P` with `[Nontrivial P]`, `SemilatticeObservableConsistent P q` holds if and only if
`Monotone q`. -/
theorem semilatticeObservableConsistent_iff_monotone {P S Out : Type*}
    [Fintype P] [DecidableEq P] [Nontrivial P] [SemilatticeSup S] [Preorder Out]
    {q : S → Out} :
    SemilatticeObservableConsistent P q ↔ Monotone q := by
  constructor
  · intro hobs s₁ s₂ hs
    obtain ⟨p₁, p₂, hp₁₂⟩ := exists_pair_ne P
    have hle := hobs (fun r => if r = p₁ then s₁ else s₂) [] p₁
    rw [globalMergedState_splitBrain hp₁₂ hs] at hle
    simpa [gossipReplicaStates] using hle
  · exact Monotone.semilatticeObservableConsistent

/-! ### Positive Monotone CRDT Query Instantiations -/

/-- Threshold fact emission on `GCounter Q` (`k ≤ c.value`), e.g. quorum/threshold crossing
([Hellerstein2010], §3.4.3 & §4.1, PDF pp. 9, 11). -/
@[expose]
def gcounterThresholdEmit {Q : Type*} [Fintype Q] (k : ℕ) (c : GCounter Q) : Finset Unit :=
  if k ≤ c.value then {()} else ∅

/-- Boolean threshold observation `decide (k ≤ c.value)` on `GCounter Q`. -/
@[expose]
def gcounterThresholdBool {Q : Type*} [Fintype Q] (k : ℕ) (c : GCounter Q) : Bool :=
  decide (k ≤ c.value)

/-- Existential / element-membership fact emission on `GSet α` (`Finset α`). -/
@[expose]
def gsetMemEmit {α : Type*} [DecidableEq α] (x : α) (s : Finset α) : Finset Unit :=
  if x ∈ s then {()} else ∅

/-- Monotone relational selection-and-projection query `(s.filter (pred · = true)).image f` on
`GSet α`. -/
@[expose]
def gsetFilterImage {α β : Type*} [DecidableEq β] (pred : α → Bool) (f : α → β)
    (s : Finset α) : Finset β :=
  (s.filter (fun a => pred a = true)).image f

theorem monotone_gcounterThresholdEmit {Q : Type*} [Fintype Q] (k : ℕ) :
    Monotone (gcounterThresholdEmit (Q := Q) k) := by
  intro c₁ c₂ hc u hu
  simp only [gcounterThresholdEmit] at hu ⊢
  split_ifs at hu with h₁
  · have h₂ : k ≤ c₂.value := le_trans h₁ (GCounter.mono_value hc)
    simp [h₂]
  · cases hu

theorem semilatticeCoordinationFreeConsistent_gcounterThreshold
    (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {Q : Type*} [Fintype Q] (k : ℕ) :
    SemilatticeCoordinationFreeConsistent P (gcounterThresholdEmit (Q := Q) k) :=
  (monotone_gcounterThresholdEmit k).semilatticeCoordinationFreeConsistent

theorem monotone_gcounterThresholdBool {Q : Type*} [Fintype Q] (k : ℕ) :
    Monotone (gcounterThresholdBool (Q := Q) k) := by
  intro c₁ c₂ hc
  simp only [gcounterThresholdBool, Bool.le_iff_imp, decide_eq_true_eq]
  exact fun h => h.trans (GCounter.mono_value hc)

theorem semilatticeObservableConsistent_gcounterThresholdBool
    (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {Q : Type*} [Fintype Q] (k : ℕ) :
    SemilatticeObservableConsistent P (gcounterThresholdBool (Q := Q) k) :=
  (monotone_gcounterThresholdBool k).semilatticeObservableConsistent

theorem monotone_gsetMemEmit {α : Type*} [DecidableEq α] (x : α) :
    Monotone (gsetMemEmit x) := by
  intro s₁ s₂ hs u hu
  simp only [gsetMemEmit] at hu ⊢
  split_ifs at hu with hx
  · have hx₂ : x ∈ s₂ := hs hx
    simp [hx₂]
  · cases hu

theorem semilatticeCoordinationFreeConsistent_gsetMem
    (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {α : Type*} [DecidableEq α] (x : α) :
    SemilatticeCoordinationFreeConsistent P (gsetMemEmit x) :=
  (monotone_gsetMemEmit x).semilatticeCoordinationFreeConsistent

theorem monotone_gsetFilterImage {α β : Type*} [DecidableEq β] (pred : α → Bool) (f : α → β) :
    Monotone (gsetFilterImage pred f) :=
  fun _ _ hs => Finset.image_subset_image (Finset.filter_subset_filter _ hs)

theorem semilatticeCoordinationFreeConsistent_gsetFilterImage
    (P : Type*) [Fintype P] [DecidableEq P] [Nonempty P]
    {α β : Type*} [DecidableEq α] [DecidableEq β] (pred : α → Bool) (f : α → β) :
    SemilatticeCoordinationFreeConsistent P (gsetFilterImage pred f) :=
  (monotone_gsetFilterImage pred f).semilatticeCoordinationFreeConsistent

/-! ### Negative Non-Monotone CRDT Query Instantiations (Split-Brain Retractions) -/

/-- Emptiness fact emission on `GSet α` (`s = ∅`, [AmelootNevenVandenBussche2011], §5 Example 10,
p. 7). -/
@[expose]
def gsetIsEmptyEmit {α : Type*} [DecidableEq α] (s : Finset α) : Finset Unit :=
  if s = ∅ then {()} else ∅

/-- Exact-count fact emission on `GCounter Q` (`c.value = k`). -/
@[expose]
def gcounterExactCountEmit {Q : Type*} [Fintype Q] (k : ℕ) (c : GCounter Q) : Finset Unit :=
  if c.value = k then {()} else ∅

/-- Semilattice emptiness non-monotonicity step (toward #7502, after
[AmelootNevenVandenBussche2011], §5 Example 10, p. 7): set emptiness is non-monotone and therefore
cannot be evaluated coordination-freely without split-brain retraction over `[Nontrivial P]`. -/
theorem not_semilatticeCoordinationFreeConsistent_gsetIsEmpty
    (P : Type*) [Fintype P] [DecidableEq P] [Nontrivial P]
    {α : Type*} [DecidableEq α] [Nonempty α] :
    ¬ SemilatticeCoordinationFreeConsistent P (gsetIsEmptyEmit (α := α)) := by
  rw [semilatticeCoordinationFreeConsistent_iff_monotone]
  intro hmono
  obtain ⟨x⟩ := ‹Nonempty α›
  have hsub : gsetIsEmptyEmit (∅ : Finset α) ⊆ gsetIsEmptyEmit ({x} : Finset α) :=
    hmono (Finset.empty_subset {x})
  have hmem : () ∈ gsetIsEmptyEmit ({x} : Finset α) :=
    hsub (by simp [gsetIsEmptyEmit])
  simp [gsetIsEmptyEmit] at hmem

/-- Set difference / tombstone negation (`TwoPhaseSet.elements : s ↦ s.added \ s.removed`) is
non-monotone in `TwoPhaseSet α` and therefore suffers split-brain retraction as an irrevocable
emission query over `[Nontrivial P]`. -/
theorem not_semilatticeCoordinationFreeConsistent_twoPhaseSetElements
    (P : Type*) [Fintype P] [DecidableEq P] [Nontrivial P]
    {α : Type*} [DecidableEq α] [Nonempty α] :
    ¬ SemilatticeCoordinationFreeConsistent P (TwoPhaseSet.elements (α := α)) := by
  rw [semilatticeCoordinationFreeConsistent_iff_monotone]
  intro hmono
  obtain ⟨x⟩ := ‹Nonempty α›
  let s₁ : TwoPhaseSet α := (TwoPhaseSet.empty).add x
  let s₂ : TwoPhaseSet α := s₁.remove x
  have hle : s₁ ≤ s₂ := TwoPhaseSet.le_applyOp (.remove x) s₁
  have hmem₁ : x ∈ s₁.elements :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self x ∅, Finset.notMem_empty x⟩
  have hmem₂ : x ∈ s₂.elements := hmono hle hmem₁
  exact TwoPhaseSet.not_mem_elements_of_le_of_removed
    (Finset.mem_insert_self x s₁.removed) (le_refl s₂) |>.2 hmem₂

/-- Exact-count queries (`c.value = k`) on `GCounter Q` (`[Nonempty Q]`) fail monotonicity for
every `k : ℕ` and therefore cannot be evaluated coordination-freely without split-brain retraction
over `[Nontrivial P]`. -/
theorem not_semilatticeCoordinationFreeConsistent_gcounterExactCount
    (P : Type*) [Fintype P] [DecidableEq P] [Nontrivial P]
    {Q : Type*} [Fintype Q] [Nonempty Q] (k : ℕ) :
    ¬ SemilatticeCoordinationFreeConsistent P (gcounterExactCountEmit (Q := Q) k) := by
  classical
  rw [semilatticeCoordinationFreeConsistent_iff_monotone]
  intro hmono
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  let c₁ : GCounter Q := ⟨Function.update 0 q₀ k⟩
  let c₂ : GCounter Q := c₁.inc q₀
  have hc₁_val : c₁.value = k := by
    simp only [GCounter.value, c₁]
    rw [Finset.sum_eq_single q₀ (fun x _ hx => Function.update_of_ne hx ..) (by simp),
      Function.update_self]
  have hmem₂ : () ∈ gcounterExactCountEmit k c₂ :=
    hmono (GCounter.le_inc q₀ c₁) (by simp [gcounterExactCountEmit, hc₁_val])
  simp [gcounterExactCountEmit, c₂, GCounter.value_inc, hc₁_val] at hmem₂

end Cslib.Distributed.CRDT
