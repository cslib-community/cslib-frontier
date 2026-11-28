/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Distributed.CausalBroadcast.Causal
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Basic

/-!
# State-Based and Operation-Based Conflict-Free Replicated Data Types (`CvRDT` and `CmRDT`)

This module formalizes foundational steps toward #7502 for **Conflict-Free Replicated Data Types**
and **Strong Eventual Consistency (`SEC`)** (after Shapiro, Preguiça, Baquero, and Zawirski
[ShapiroPreguicaBaqueroZawirski2011], §§2.1–2.4, §3.2, Theorems 2.1–2.2 & 3.1–3.2, and
[ShapiroPreguicaBaqueroZawirski2011R], §§2.2–2.4, Propositions 2.1–2.2 & Specifications 3–4):

1. **State-Based Convergent Replicated Data Types (`CvRDT`):**
   Reuses Mathlib's `SemilatticeSup S` with binary state merge `(· ⊔ ·)` and inflationary local
   updates (`s ≤ update op s`). Models asynchronous gossip networks (`CvRDT.gossipLTS`) over an
   arbitrary directed communication graph `Digraph P` with out-of-order message arrival, packet
   drops, and arbitrary packet duplication, proving:
   * order- and duplicate-independent state-list folding (`foldl_sup_eq_of_mem_iff`),
   * the semilattice causal-history invariant (`CvRDT.replica_eq_evalHistory`),
   * **State-Based Strong Convergence (`CvRDT.strong_convergence`):** any two replicas that have
     received the same set of updates—in any order and with any duplicates—have identical states,
   * **Strongly Connected Gossip Convergence (`CvRDT.converge_of_allPairsReachable`):** from any
     reachable configuration over a strongly connected `Digraph P`, a finite gossip wave brings all
     replicas to identical causal histories and identical states.

2. **Operation-Based Commutative Replicated Data Types (`CmRDT`) & `CausalBroadcast` Bridge:**
   Models two-phase `(prepare, effect)` replicated objects with concurrent downstream commutativity
   (`ConcurrentCommute`: `¬ prec e₁ e₂ → ¬ prec e₂ e₁ → effect (effOf e₁) (effect (effOf e₂) s) =
   effect (effOf e₂) (effect (effOf e₁) s)`), proving:
   * **Op-Based Strong Convergence (`CmRDT.causalLinearization_eq`):** every causal linearization
     (`IsCausalLinearization`) of the same finite event set produces the exact same replica state,
   * **Vector-Clock Causal Broadcast Bridge (`CmRDT.bss_strong_convergence`,
     `CmRDT.bss_quiescent_convergence`):** connects `Cslib.Distributed.CausalBroadcast`'s
     Birman–Schiper–Stephenson `bssLTS F` directly to `CmRDT` strong convergence across all
     processes (faulty or correct) and eventual quiescent convergence across all non-crashed
     processes `q ∉ F` for any static crash-fault set `F : Set P`.

3. **State/Op Emulation Equivalence (`CvRDT.toCmRDT`, `CmRDT.toCvRDT`):**
   * `CvRDT.toCmRDT` emulates any `CvRDT` as an unconditionally commutative `CmRDT` by broadcasting
     post-update states and merging downstream via `(· ⊔ ·)` (`CvRDT.toCmRDT_effectsCommute`,
     `CvRDT.toCmRDT_foldl_eq_evalHistory`).
   * `CmRDT.toCvRDT` emulates any `CmRDT` as a state-based `CvRDT` over finite event sets
     `Finset Ev` ordered by `(⊆)` with merge `(· ∪ ·)`, extracting the maximal `deps`-closed
     deliverable subset (`deliverableEvents`) and evaluating any causal linearization
     (`CmRDT.evalCausalSet`), agreeing with op-based `CmRDT` execution on all causally closed
     histories.

## Model scope relative to primary sources

[ShapiroPreguicaBaqueroZawirski2011] (§5) and [ShapiroPreguicaBaqueroZawirski2011R] (§§3.2, 3.4–3.5,
4) additionally study `LWW-Register`, `MV-Register`, graph and sequence CRDTs (`2P2P-Graph`,
monotonic DAGs, `RGA`/`Treedoc`), and Wuu–Bernstein vector-clock garbage collection, which remain
open under #7502. Concrete counter and set data types (`GCounter`, `PNCounter`, `TwoPhaseSet`,
`ORSet`) are developed in `CslibFrontier.Computability.Distributed.CRDT.DataTypes`.

## Main definitions

* `Cslib.Distributed.CRDT.CvRDT`: state-based convergent replicated data type over
  `[SemilatticeSup S]` with `update_infl : ∀ op s, s ≤ update op s`.
* `Cslib.Distributed.CRDT.evalHistory`: semilattice supremum of `init` and `postState` over a finite
  causal history `Finset UId`.
* `Cslib.Distributed.CRDT.GossipPacket`,
  `Cslib.Distributed.CRDT.GossipState`,
  `Cslib.Distributed.CRDT.GossipAction`,
  `Cslib.Distributed.CRDT.CvRDT.gossipLTS`: asynchronous state-based gossip transition system with
  reordering, packet loss, and arbitrary packet duplication.
* `Cslib.Distributed.CRDT.CmRDT`: operation-based replicated data type with `prepare` and
  downstream `effect`.
* `Cslib.Distributed.CRDT.EffectsCommute`,
  `Cslib.Distributed.CRDT.ConcurrentCommute`,
  `Cslib.Distributed.CRDT.IsCausallyClosed`,
  `Cslib.Distributed.CRDT.IsCausalLinearization`: unconditional vs. concurrent downstream
  commutativity, causal closure, and duplicate-free causal linearizations.
* `Cslib.Distributed.CRDT.CmRDT.bssReplicaState`: `CmRDT` replica state induced by the `delivered`
  log of `Cslib.Distributed.CausalBroadcast.BSSState`.
* `Cslib.Distributed.CRDT.CvRDT.toCmRDT`,
  `Cslib.Distributed.CRDT.deliverableEvents`,
  `Cslib.Distributed.CRDT.CmRDT.evalCausalSet`,
  `Cslib.Distributed.CRDT.CmRDT.toCvRDT`: bidirectional emulations between `CvRDT` and `CmRDT`.

## Main results

* `Cslib.Distributed.CRDT.foldl_sup_eq_of_mem_iff`: merging two state lists via `(· ⊔ ·)` yields
  identical results whenever they contain the same set of elements, regardless of order or
  duplicates.
* `Cslib.Distributed.CRDT.CvRDT.replica_eq_evalHistory` and
  `Cslib.Distributed.CRDT.CvRDT.strong_convergence`: state-based `SEC` step over `gossipLTS`
  (`s.history p = s.history q → s.replica p = s.replica q`).
* `Cslib.Distributed.CRDT.CvRDT.converge_of_allPairsReachable`: finite-wave gossip convergence step
  across any strongly connected `Digraph P`.
* `Cslib.Distributed.CRDT.CmRDT.causalLinearization_eq`: op-based `SEC` step showing any two causal
  linearizations of a finite event set with commuting concurrent effects evaluate to the exact same
  state.
* `Cslib.Distributed.CRDT.CmRDT.bss_strong_convergence` and
  `Cslib.Distributed.CRDT.CmRDT.bss_quiescent_convergence`: causal-broadcast bridge steps over
  `CausalBroadcast.bssLTS F` for arbitrary crash-fault sets `F : Set P`.
* `Cslib.Distributed.CRDT.CvRDT.toCmRDT_effectsCommute` and
  `Cslib.Distributed.CRDT.CvRDT.toCmRDT_foldl_eq_evalHistory`: op-based emulation of any `CvRDT`.
* `Cslib.Distributed.CRDT.exists_causalLinearization`,
  `Cslib.Distributed.CRDT.CmRDT.evalCausalSet_eq_foldl`,
  `Cslib.Distributed.CRDT.CmRDT.evalCausalSet_insert_max`, and
  `Cslib.Distributed.CRDT.CmRDT.toCvRDT_query_eq`: state-based `CvRDT` emulation of any `CmRDT`.

## References

* [M. Shapiro, N. Preguiça, C. Baquero, M. Zawirski, *Conflict-free Replicated Data
  Types*][ShapiroPreguicaBaqueroZawirski2011]
* [M. Shapiro, N. Preguiça, C. Baquero, M. Zawirski, *A comprehensive study of Convergent and
  Commutative Replicated Data Types*][ShapiroPreguicaBaqueroZawirski2011R]
-/

public section

namespace Cslib.Distributed.CRDT

open Cslib Cslib.ωSequence Cslib.Distributed.CausalBroadcast

/-! ### Semilattice list and history folding -/

section SemilatticeFold

variable {S α UId : Type*} [SemilatticeSup S]

private theorem init_le_foldl_sup (s₀ : S) (f : α → S) (l : List α) :
    s₀ ≤ l.foldl (fun s a => s ⊔ f a) s₀ := by
  induction l generalizing s₀ with
  | nil => exact le_rfl
  | cons a tl ih => exact le_trans le_sup_left (ih (s₀ ⊔ f a))

private theorem mem_le_foldl_sup (s₀ : S) (f : α → S) {l : List α} {a : α} (ha : a ∈ l) :
    f a ≤ l.foldl (fun s x => s ⊔ f x) s₀ := by
  induction l generalizing s₀ with
  | nil => cases ha
  | cons hd tl ih =>
    rcases List.mem_cons.mp ha with rfl | htl
    · exact le_trans le_sup_right (init_le_foldl_sup (s₀ ⊔ f a) f tl)
    · exact ih (s₀ ⊔ f hd) htl

private theorem foldl_sup_le (s₀ : S) (f : α → S) (l : List α) {u : S}
    (hs₀ : s₀ ≤ u) (hl : ∀ a ∈ l, f a ≤ u) :
    l.foldl (fun s a => s ⊔ f a) s₀ ≤ u := by
  induction l generalizing s₀ with
  | nil => exact hs₀
  | cons hd tl ih =>
    exact ih (s₀ ⊔ f hd)
      (sup_le hs₀ (hl hd List.mem_cons_self))
      (fun a ha => hl a (List.mem_cons_of_mem hd ha))

/-- Order- and duplicate-independence of semilattice merges: folding `(· ⊔ ·)` over two lists
from `s₀` yields the exact same state whenever the lists have the same support set, regardless of
arrival order or multiplicity. -/
theorem foldl_sup_eq_of_mem_iff (s₀ : S) (f : α → S) {l₁ l₂ : List α}
    (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) :
    l₁.foldl (fun s a => s ⊔ f a) s₀ = l₂.foldl (fun s a => s ⊔ f a) s₀ := by
  apply le_antisymm
  · exact foldl_sup_le s₀ f l₁ (init_le_foldl_sup s₀ f l₂)
      (fun a ha => mem_le_foldl_sup s₀ f ((hmem a).mp ha))
  · exact foldl_sup_le s₀ f l₂ (init_le_foldl_sup s₀ f l₁)
      (fun a ha => mem_le_foldl_sup s₀ f ((hmem a).mpr ha))

/-- Evaluate the semilattice supremum of `init` together with the post-states `post u` of all
update identifiers `u ∈ H` ([ShapiroPreguicaBaqueroZawirski2011], §2.1 & §2.3, pp. 5–7). -/
@[expose]
def evalHistory (init : S) (post : UId → S) (H : Finset UId) : S :=
  H.fold (· ⊔ ·) init post

@[simp]
theorem evalHistory_empty (init : S) (post : UId → S) :
    evalHistory init post (∅ : Finset UId) = init :=
  Finset.fold_empty

/-- Universal least-upper-bound characterization of `evalHistory init post H`. -/
theorem evalHistory_le_iff {init : S} {post : UId → S}
    {H : Finset UId} {b : S} :
    evalHistory init post H ≤ b ↔ init ≤ b ∧ ∀ u ∈ H, post u ≤ b := by
  induction H using Finset.cons_induction with
  | empty => simp [evalHistory]
  | cons u H hu ih =>
    simp only [evalHistory, Finset.fold_cons hu, sup_le_iff, Finset.mem_cons, forall_eq_or_imp]
    rw [← evalHistory, ih]
    tauto

theorem init_le_evalHistory (init : S) (post : UId → S) (H : Finset UId) :
    init ≤ evalHistory init post H :=
  (evalHistory_le_iff.mp le_rfl).1

theorem mem_le_evalHistory {init : S} {post : UId → S}
    {H : Finset UId} {u : UId} (hu : u ∈ H) :
    post u ≤ evalHistory init post H :=
  (evalHistory_le_iff.mp le_rfl).2 u hu

@[simp]
theorem evalHistory_insert [DecidableEq UId] (init : S) (post : UId → S)
    (u : UId) (H : Finset UId) :
    evalHistory init post (insert u H) = post u ⊔ evalHistory init post H := by
  refine eq_of_forall_ge_iff fun b => ?_
  simp only [evalHistory_le_iff, sup_le_iff, Finset.mem_insert, forall_eq_or_imp]
  tauto

@[simp]
theorem evalHistory_union [DecidableEq UId] (init : S) (post : UId → S)
    (H₁ H₂ : Finset UId) :
    evalHistory init post (H₁ ∪ H₂) =
      evalHistory init post H₁ ⊔ evalHistory init post H₂ := by
  refine eq_of_forall_ge_iff fun b => ?_
  simp only [evalHistory_le_iff, sup_le_iff, Finset.mem_union, or_imp, forall_and]
  tauto

theorem evalHistory_congr (init : S) {post₁ post₂ : UId → S}
    {H : Finset UId} (h : ∀ u ∈ H, post₁ u = post₂ u) :
    evalHistory init post₁ H = evalHistory init post₂ H :=
  Finset.fold_congr h

theorem foldl_sup_eq_evalHistory (init : S) (post : UId → S)
    (l : List UId) (H : Finset UId) (hmem : ∀ u, u ∈ l ↔ u ∈ H) :
    l.foldl (fun s u => s ⊔ post u) init = evalHistory init post H := by
  apply le_antisymm
  · exact foldl_sup_le init post l (init_le_evalHistory init post H)
      (fun u hu => mem_le_evalHistory ((hmem u).mp hu))
  · rw [evalHistory_le_iff]
    exact ⟨init_le_foldl_sup init post l,
      fun u hu => mem_le_foldl_sup init post ((hmem u).mpr hu)⟩

end SemilatticeFold

/-! ### State-based Convergent Replicated Data Types (`CvRDT`) -/

/-- A state-based **Convergent Replicated Data Type (`CvRDT`)** (monotonic semilattice object,
after [ShapiroPreguicaBaqueroZawirski2011], §2.3, Definition 2.4, p. 6;
[ShapiroPreguicaBaqueroZawirski2011R], §2.3.1, p. 10) over Mathlib's `SemilatticeSup S`:
replicas start at `init`, answer local queries via `query`, merge remote payloads via semilattice
supremum `(· ⊔ ·)`, and advance monotonically across local updates (`s ≤ update op s`). -/
structure CvRDT (S Op Q : Type*) [SemilatticeSup S] where
  /-- Initial state `s⁰` of every replica. -/
  init : S
  /-- Side-effect-free local query `q : S → Q`. -/
  query : S → Q
  /-- Local mutating update operation `u : Op → S → S`. -/
  update : Op → S → S
  /-- Monotonicity (inflationarity) of updates in the semilattice: `s ≤ update op s`. -/
  update_infl : ∀ op s, s ≤ update op s

/-- An in-flight gossip packet addressed to `dest`, carrying state `payload : S` together with the
ghost causal history `ghostHist` of update identifiers reflected in `payload`
([ShapiroPreguicaBaqueroZawirski2011], §2.1, Definition 2.1, p. 5). Note that replica merge steps
inspect only `dest` and `payload`; `ghostHist` is purely a specification field. -/
@[ext]
structure GossipPacket (P UId S : Type*) where
  /-- Recipient replica identity. -/
  dest : P
  /-- Transmitted semilattice state payload. -/
  payload : S
  /-- Ghost causal history of updates reflected in `payload` (never read by protocol logic). -/
  ghostHist : Finset UId
  deriving @[expose] DecidableEq

/-- Global configuration of an asynchronous state-based `CvRDT` gossip network. -/
@[ext]
structure GossipState (P UId S : Type*) where
  /-- Current semilattice state at each replica. -/
  replica : P → S
  /-- Ghost causal history `c_p` of update identifiers delivered at each replica. -/
  history : P → Finset UId
  /-- Unordered multiset of in-flight state gossip packets. -/
  inFlight : Multiset (GossipPacket P UId S)
  /-- Ghost set of unique update identifiers generated so far across all replicas. -/
  generated : Finset UId
  /-- Ghost map recording the post-update state created when each `uid` executed at its source. -/
  postState : UId → S

/-- Transition labels of the asynchronous `CvRDT` gossip network: local updates, point-to-point
state gossip sends, consuming merges, duplicate-preserving merges, and packet drops. -/
inductive GossipAction (P UId Op S : Type*) where
  /-- Replica `p` executes `op` locally with fresh update identifier `uid`. -/
  | update (p : P) (uid : UId) (op : Op)
  /-- Replica `src` sends its current state to neighbor `dst`. -/
  | send (src dst : P)
  /-- Replica `pkt.dest` merges `pkt.payload` via `(· ⊔ ·)` and consumes `pkt` from `inFlight`. -/
  | mergeConsume (pkt : GossipPacket P UId S)
  /-- Replica `pkt.dest` merges `pkt.payload` via `(· ⊔ ·)` while keeping `pkt` in `inFlight`
  (modeling arbitrary network packet duplication). -/
  | mergeDuplicate (pkt : GossipPacket P UId S)
  /-- Network drops an in-flight packet `pkt` (modeling lossy links or temporary partitions). -/
  | drop (pkt : GossipPacket P UId S)
  deriving @[expose] DecidableEq

section CvRDTGossip

variable {P UId S Op Q : Type*} [DecidableEq P] [DecidableEq UId] [DecidableEq S]
  [SemilatticeSup S]

/-- Initial global gossip configuration for `C : CvRDT S Op Q`: all replicas start at `C.init` with
empty causal histories and empty channels. -/
@[expose]
def CvRDT.gossipInit (C : CvRDT S Op Q) : GossipState P UId S where
  replica := fun _ => C.init
  history := fun _ => ∅
  inFlight := 0
  generated := ∅
  postState := fun _ => C.init

/-- Deterministic state update for one `GossipAction` of `C : CvRDT S Op Q`. -/
@[expose]
def CvRDT.gossipStep (C : CvRDT S Op Q) (s : GossipState P UId S) :
    GossipAction P UId Op S → GossipState P UId S
  | .update p uid op =>
      let s' := C.update op (s.replica p)
      { replica := Function.update s.replica p s'
        history := Function.update s.history p (insert uid (s.history p))
        inFlight := s.inFlight
        generated := insert uid s.generated
        postState := Function.update s.postState uid s' }
  | .send src dst =>
      { s with inFlight := ⟨dst, s.replica src, s.history src⟩ ::ₘ s.inFlight }
  | .mergeConsume pkt =>
      let q := pkt.dest
      { s with
        replica := Function.update s.replica q (s.replica q ⊔ pkt.payload)
        history := Function.update s.history q (s.history q ∪ pkt.ghostHist)
        inFlight := s.inFlight.erase pkt }
  | .mergeDuplicate pkt =>
      let q := pkt.dest
      { s with
        replica := Function.update s.replica q (s.replica q ⊔ pkt.payload)
        history := Function.update s.history q (s.history q ∪ pkt.ghostHist) }
  | .drop pkt =>
      { s with inFlight := s.inFlight.erase pkt }

/-- Enabledness guard for `GossipAction` over directed communication graph `G : Digraph P`. -/
@[expose]
def CvRDT.GossipEnabled (_C : CvRDT S Op Q) (G : Digraph P) (s : GossipState P UId S) :
    GossipAction P UId Op S → Prop
  | .update _ uid _ => uid ∉ s.generated
  | .send src dst => G.Adj src dst
  | .mergeConsume pkt => pkt ∈ s.inFlight
  | .mergeDuplicate pkt => pkt ∈ s.inFlight
  | .drop pkt => pkt ∈ s.inFlight

instance (C : CvRDT S Op Q) (G : Digraph P) [DecidableRel G.Adj] (s : GossipState P UId S) :
    DecidablePred (C.GossipEnabled G s) := fun act =>
  match act with
  | .update _ _ _ => inferInstanceAs (Decidable (_ ∉ _))
  | .send _ _ => inferInstanceAs (Decidable (G.Adj _ _))
  | .mergeConsume _ => inferInstanceAs (Decidable (_ ∈ _))
  | .mergeDuplicate _ => inferInstanceAs (Decidable (_ ∈ _))
  | .drop _ => inferInstanceAs (Decidable (_ ∈ _))

/-- Asynchronous gossip labelled transition system (`Cslib.LTS`) of `C : CvRDT S Op Q` over
communication graph `G : Digraph P`. -/
@[expose]
def CvRDT.gossipLTS (C : CvRDT S Op Q) (G : Digraph P) :
    LTS (GossipState P UId S) (GossipAction P UId Op S) where
  Tr s act s' := C.GossipEnabled G s act ∧ s' = C.gossipStep s act

/-- Fold a finite list of `GossipAction`s starting from `s₀`. -/
@[expose]
def CvRDT.gossipRun (C : CvRDT S Op Q) (s₀ : GossipState P UId S)
    (xl : List (GossipAction P UId Op S)) : GossipState P UId S :=
  xl.foldl C.gossipStep s₀

/-- Check whether every action in `xl` is enabled from `s₀` over communication graph `G`. -/
@[expose]
def CvRDT.gossipValidTrace (C : CvRDT S Op Q) (G : Digraph P) :
    GossipState P UId S → List (GossipAction P UId Op S) → Prop
  | _, [] => True
  | s, act :: xl => C.GossipEnabled G s act ∧ C.gossipValidTrace G (C.gossipStep s act) xl

instance instDecidableGossipValidTrace (C : CvRDT S Op Q) (G : Digraph P) [DecidableRel G.Adj]
    (s : GossipState P UId S) :
    (xl : List (GossipAction P UId Op S)) → Decidable (C.gossipValidTrace G s xl)
  | [] => isTrue trivial
  | act :: xl =>
      letI := instDecidableGossipValidTrace C G (C.gossipStep s act) xl
      inferInstanceAs
        (Decidable (C.GossipEnabled G s act ∧ C.gossipValidTrace G (C.gossipStep s act) xl))

/-- Equivalence between `LTS.MTr` on `C.gossipLTS G` and `C.gossipValidTrace` + `C.gossipRun`. -/
theorem CvRDT.gossipLTS_mTr_iff (C : CvRDT S Op Q) (G : Digraph P)
    (s₀ : GossipState P UId S) (xl : List (GossipAction P UId Op S)) (s : GossipState P UId S) :
    (C.gossipLTS G).MTr s₀ xl s ↔ C.gossipValidTrace G s₀ xl ∧ s = C.gossipRun s₀ xl := by
  induction xl generalizing s₀ with
  | nil => exact ⟨fun | .refl => ⟨trivial, rfl⟩, fun ⟨_, h⟩ => h ▸ .refl⟩
  | cons act xl ih =>
    exact
      ⟨fun | .stepL htr hmtr =>
             let ⟨hv, hs⟩ := htr.2 ▸ (ih _).mp hmtr
             ⟨⟨htr.1, hv⟩, hs⟩,
       fun ⟨⟨hen, hv⟩, h⟩ => .stepL ⟨hen, rfl⟩ ((ih _).mpr ⟨hv, h⟩)⟩

private structure GossipInv (C : CvRDT S Op Q) (s : GossipState P UId S) : Prop where
  hist_sub : ∀ p, s.history p ⊆ s.generated
  pkt_sub : ∀ pkt ∈ s.inFlight, pkt.ghostHist ⊆ s.generated
  rep_eq : ∀ p, s.replica p = evalHistory C.init s.postState (s.history p)
  pkt_eq : ∀ pkt ∈ s.inFlight, pkt.payload = evalHistory C.init s.postState pkt.ghostHist

omit [DecidableEq P] [DecidableEq UId] [DecidableEq S] in
private theorem gossipInv_init (C : CvRDT S Op Q) :
    GossipInv C (C.gossipInit : GossipState P UId S) where
  hist_sub _ := Finset.Subset.refl _
  pkt_sub _ hp := by simp [CvRDT.gossipInit] at hp
  rep_eq _ := by simp [CvRDT.gossipInit]
  pkt_eq _ hp := by simp [CvRDT.gossipInit] at hp

private theorem gossipInv_step (C : CvRDT S Op Q) {G : Digraph P}
    {s : GossipState P UId S} {act : GossipAction P UId Op S}
    (hinv : GossipInv C s) (hen : C.GossipEnabled G s act) :
    GossipInv C (C.gossipStep s act) := by
  have hmerge_local : ∀ pkt ∈ s.inFlight,
      (∀ q, Function.update s.history pkt.dest (s.history pkt.dest ∪ pkt.ghostHist) q ⊆
        s.generated) ∧
      (∀ q, Function.update s.replica pkt.dest (s.replica pkt.dest ⊔ pkt.payload) q =
        evalHistory C.init s.postState
          (Function.update s.history pkt.dest (s.history pkt.dest ∪ pkt.ghostHist) q)) := by
    intro pkt hpkt_in
    refine ⟨fun q => ?_, fun q => ?_⟩ <;> simp only [Function.update_apply] <;> split_ifs with hq
    · exact Finset.union_subset (hinv.hist_sub _) (hinv.pkt_sub pkt hpkt_in)
    · exact hinv.hist_sub q
    · simp [evalHistory_union, ← hinv.rep_eq pkt.dest, ← hinv.pkt_eq pkt hpkt_in]
    · exact hinv.rep_eq q
  cases act with
  | update p uid op =>
    have huid_not : uid ∉ s.generated := hen
    have hcongr_hist (q) :
        evalHistory C.init (Function.update s.postState uid (C.update op (s.replica p)))
          (s.history q) = evalHistory C.init s.postState (s.history q) :=
      evalHistory_congr C.init fun u hu =>
        Function.update_of_ne (fun heq => huid_not (heq ▸ hinv.hist_sub q hu : uid ∈ _)) _ _
    refine ⟨fun q => ?_,
      fun pkt hpkt => (hinv.pkt_sub pkt hpkt).trans (Finset.subset_insert uid s.generated),
      fun q => ?_, fun pkt hpkt => ?_⟩
    · simp only [CvRDT.gossipStep, Function.update_apply]
      split_ifs
      · exact Finset.insert_subset_insert uid (hinv.hist_sub p)
      · exact (hinv.hist_sub q).trans (Finset.subset_insert uid s.generated)
    · rcases eq_or_ne q p with rfl | hqp
      · simp only [CvRDT.gossipStep, Function.update_self, evalHistory_insert, hcongr_hist q,
          ← hinv.rep_eq q]
        exact (sup_of_le_left (C.update_infl op (s.replica q))).symm
      · simpa only [CvRDT.gossipStep, Function.update_of_ne hqp, hcongr_hist q] using hinv.rep_eq q
    · rw [hinv.pkt_eq pkt hpkt]
      exact evalHistory_congr C.init fun u hu =>
        (Function.update_of_ne
          (fun heq => huid_not (heq ▸ hinv.pkt_sub pkt hpkt hu : uid ∈ _)) _ _).symm
  | send src dst =>
    refine ⟨hinv.hist_sub, fun pkt hpkt => ?_, hinv.rep_eq, fun pkt hpkt => ?_⟩
    · exact (Multiset.mem_cons.mp hpkt).elim (fun h => h ▸ hinv.hist_sub src) (hinv.pkt_sub pkt)
    · exact (Multiset.mem_cons.mp hpkt).elim (fun h => h ▸ hinv.rep_eq src) (hinv.pkt_eq pkt)
  | mergeConsume pkt =>
    exact ⟨(hmerge_local pkt hen).1,
      fun m hm => hinv.pkt_sub m (Multiset.mem_of_mem_erase hm),
      (hmerge_local pkt hen).2,
      fun m hm => hinv.pkt_eq m (Multiset.mem_of_mem_erase hm)⟩
  | mergeDuplicate pkt =>
    exact ⟨(hmerge_local pkt hen).1, hinv.pkt_sub, (hmerge_local pkt hen).2, hinv.pkt_eq⟩
  | drop pkt =>
    exact ⟨hinv.hist_sub, fun m hm => hinv.pkt_sub m (Multiset.mem_of_mem_erase hm),
      hinv.rep_eq, fun m hm => hinv.pkt_eq m (Multiset.mem_of_mem_erase hm)⟩

private theorem gossipInv_mTr (C : CvRDT S Op Q) {G : Digraph P}
    {s₀ s : GossipState P UId S} {xl : List (GossipAction P UId Op S)}
    (hinv₀ : GossipInv C s₀) (hmtr : (C.gossipLTS G).MTr s₀ xl s) :
    GossipInv C s := by
  induction hmtr with
  | refl => exact hinv₀
  | stepL htr _ ih =>
    rcases htr with ⟨hen, rfl⟩
    exact ih (gossipInv_step C hinv₀ hen)

/-- Semilattice causal-history invariant step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §2.3, Theorem 2.1, pp. 6–7): in any finite execution of
`C.gossipLTS G` from `C.gossipInit`, each replica's concrete payload equals the semilattice
supremum `evalHistory C.init s.postState (s.history p)` of its delivered update history. -/
theorem CvRDT.replica_eq_evalHistory (C : CvRDT S Op Q) {G : Digraph P}
    {xl : List (GossipAction P UId Op S)} {s : GossipState P UId S}
    (hmtr : (C.gossipLTS G).MTr C.gossipInit xl s) (p : P) :
    s.replica p = evalHistory C.init s.postState (s.history p) :=
  (gossipInv_mTr C (gossipInv_init C) hmtr).rep_eq p

/-- State-based Strong Eventual Consistency (`SEC`) strong-convergence step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §2.2 Definition 2.3 & §2.3 Theorem 2.1, pp. 5–7): along any
finite execution of `C.gossipLTS G` (allowing arbitrary packet delay, reordering, loss, and
duplication), any two replicas `p` and `q` that have delivered the same update set (`s.history p =
s.history q`) have identical states (`s.replica p = s.replica q`) and identical query results. -/
theorem CvRDT.strong_convergence (C : CvRDT S Op Q) {G : Digraph P}
    {xl : List (GossipAction P UId Op S)} {s : GossipState P UId S}
    (hmtr : (C.gossipLTS G).MTr C.gossipInit xl s) {p q : P}
    (hhist : s.history p = s.history q) :
    s.replica p = s.replica q ∧ C.query (s.replica p) = C.query (s.replica q) := by
  have hrep : s.replica p = s.replica q := by
    rw [C.replica_eq_evalHistory hmtr p, C.replica_eq_evalHistory hmtr q, hhist]
  exact ⟨hrep, congrArg C.query hrep⟩

private theorem gossip_edge_hop (C : CvRDT S Op Q) {G : Digraph P}
    (s : GossipState P UId S) {u v : P} (hadj : G.Adj u v) :
    ∃ (xl : List (GossipAction P UId Op S)) (s' : GossipState P UId S),
      (C.gossipLTS G).MTr s xl s' ∧
      s'.generated = s.generated ∧
      (∀ w, s.replica w ≤ s'.replica w) ∧
      (∀ w, s.history w ⊆ s'.history w) ∧
      s.replica u ≤ s'.replica v ∧
      s.history u ⊆ s'.history v ∧
      (∀ b, (∀ w, s.replica w ≤ b) → ∀ w, s'.replica w ≤ b) ∧
      (∀ H, (∀ w, s.history w ⊆ H) → ∀ w, s'.history w ⊆ H) := by
  let pkt : GossipPacket P UId S := ⟨v, s.replica u, s.history u⟩
  let s₁ := C.gossipStep s (.send u v)
  let s₂ := C.gossipStep s₁ (.mergeConsume pkt)
  refine ⟨[.send u v, .mergeConsume pkt], s₂,
    LTS.MTr.stepL ⟨hadj, rfl⟩ (LTS.MTr.stepL ⟨Multiset.mem_cons_self pkt s.inFlight, rfl⟩
      LTS.MTr.refl), rfl, fun w => ?_, fun w => ?_, ?_, ?_, fun b hb w => ?_, fun H hH w => ?_⟩
  all_goals simp only [s₂, s₁, CvRDT.gossipStep, pkt, Function.update_apply]
  · split_ifs with hwv <;> simp [hwv]
  · split_ifs with hwv <;> simp [hwv]
  · exact le_sup_right
  · exact Finset.subset_union_right
  · split_ifs <;> simp [hb]
  · split_ifs <;> simp [hH]

private theorem gossip_walk_propagate (C : CvRDT S Op Q) {G : Digraph P}
    {u v : P} (hpath : Relation.ReflTransGen G.Adj u v) (s : GossipState P UId S) :
    ∃ (xl : List (GossipAction P UId Op S)) (s' : GossipState P UId S),
      (C.gossipLTS G).MTr s xl s' ∧
      s'.generated = s.generated ∧
      (∀ w, s.replica w ≤ s'.replica w) ∧
      (∀ w, s.history w ⊆ s'.history w) ∧
      s.replica u ≤ s'.replica v ∧
      s.history u ⊆ s'.history v ∧
      (∀ b, (∀ w, s.replica w ≤ b) → ∀ w, s'.replica w ≤ b) ∧
      (∀ H, (∀ w, s.history w ⊆ H) → ∀ w, s'.history w ⊆ H) := by
  induction hpath generalizing s with
  | refl =>
    exact ⟨[], s, LTS.MTr.refl, rfl, fun _ => le_rfl, fun _ => Finset.Subset.refl _,
      le_rfl, Finset.Subset.refl _, fun _ hb => hb, fun _ hH => hH⟩
  | tail _ hadj ih =>
    obtain ⟨xl₁, s₁, hmtr₁, hgen₁, hrep_le₁, hhist_sub₁, hu_mid_rep, hu_mid_hist,
      hrep_ub₁, hhist_ub₁⟩ := ih s
    obtain ⟨xl₂, s₂, hmtr₂, hgen₂, hrep_le₂, hhist_sub₂, hmid_v_rep, hmid_v_hist,
      hrep_ub₂, hhist_ub₂⟩ := gossip_edge_hop C s₁ hadj
    exact ⟨xl₁ ++ xl₂, s₂, LTS.MTr.comp (C.gossipLTS G) hmtr₁ hmtr₂, hgen₂.trans hgen₁,
      fun w => le_trans (hrep_le₁ w) (hrep_le₂ w),
      fun w => Finset.Subset.trans (hhist_sub₁ w) (hhist_sub₂ w),
      le_trans hu_mid_rep hmid_v_rep,
      Finset.Subset.trans hu_mid_hist hmid_v_hist,
      fun b hb => hrep_ub₂ b (hrep_ub₁ b hb),
      fun H hH => hhist_ub₂ H (hhist_ub₁ H hH)⟩

private theorem gossip_propagate_list (C : CvRDT S Op Q) {G : Digraph P}
    (hreach : ∀ p q : P, Relation.ReflTransGen G.Adj p q)
    (pairs : List (P × P)) (s : GossipState P UId S) :
    ∃ (xl : List (GossipAction P UId Op S)) (s' : GossipState P UId S),
      (C.gossipLTS G).MTr s xl s' ∧
      s'.generated = s.generated ∧
      (∀ w, s.replica w ≤ s'.replica w) ∧
      (∀ w, s.history w ⊆ s'.history w) ∧
      (∀ p q, (p, q) ∈ pairs → s.replica p ≤ s'.replica q ∧ s.history p ⊆ s'.history q) ∧
      (∀ b, (∀ w, s.replica w ≤ b) → ∀ w, s'.replica w ≤ b) ∧
      (∀ H, (∀ w, s.history w ⊆ H) → ∀ w, s'.history w ⊆ H) := by
  induction pairs generalizing s with
  | nil =>
    exact ⟨[], s, LTS.MTr.refl, rfl, fun _ => le_rfl, fun _ => Finset.Subset.refl _,
      by simp, fun _ hb => hb, fun _ hH => hH⟩
  | cons hd tl ih =>
    obtain ⟨u, v⟩ := hd
    obtain ⟨xl₁, s₁, hmtr₁, hgen₁, hrep₁, hhist₁, huv_rep, huv_hist, hub_rep₁, hub_hist₁⟩ :=
      gossip_walk_propagate C (hreach u v) s
    obtain ⟨xl₂, s₂, hmtr₂, hgen₂, hrep₂, hhist₂, htl, hub_rep₂, hub_hist₂⟩ := ih s₁
    refine ⟨xl₁ ++ xl₂, s₂, LTS.MTr.comp (C.gossipLTS G) hmtr₁ hmtr₂, hgen₂.trans hgen₁,
      fun w => le_trans (hrep₁ w) (hrep₂ w),
      fun w => Finset.Subset.trans (hhist₁ w) (hhist₂ w), ?_,
      fun b hb => hub_rep₂ b (hub_rep₁ b hb),
      fun H hH => hub_hist₂ H (hub_hist₁ H hH)⟩
    intro p q hpq
    rcases List.mem_cons.mp hpq with hhd | hmem_tl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhd
      exact ⟨le_trans huv_rep (hrep₂ q), Finset.Subset.trans huv_hist (hhist₂ q)⟩
    · obtain ⟨hr, hh⟩ := htl p q hmem_tl
      exact ⟨le_trans (hrep₁ p) hr, Finset.Subset.trans (hhist₁ p) hh⟩

/-- Strongly connected gossip eventual-convergence step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §2.3 Theorem 2.1, pp. 6–7;
[ShapiroPreguicaBaqueroZawirski2011R], §2.3.1 Proposition 2.1, p. 10): from any state `s` over a
finite strongly connected graph `G : Digraph P` (`∀ p q, Relation.ReflTransGen G.Adj p q`), there
exists a finite gossip wave with no new client updates reaching `s'` where every replica holds the
global supremum `Finset.univ.sup' Finset.univ_nonempty s.replica` and the global history union
`Finset.univ.biUnion s.history`. -/
theorem CvRDT.converge_of_allPairsReachable [Fintype P] [Nonempty P]
    (C : CvRDT S Op Q) {G : Digraph P}
    (hreach : ∀ p q : P, Relation.ReflTransGen G.Adj p q)
    (s : GossipState P UId S) :
    ∃ (xl : List (GossipAction P UId Op S)) (s' : GossipState P UId S),
      (C.gossipLTS G).MTr s xl s' ∧
      s'.generated = s.generated ∧
      (∀ p : P, s'.replica p = Finset.univ.sup' Finset.univ_nonempty s.replica) ∧
      (∀ p : P, s'.history p = Finset.univ.biUnion s.history) := by
  let allPairs : List (P × P) := ((Finset.univ : Finset P) ×ˢ (Finset.univ : Finset P)).toList
  have hmem (q p : P) : (q, p) ∈ allPairs :=
    Finset.mem_toList.mpr (Finset.mem_product.mpr ⟨Finset.mem_univ q, Finset.mem_univ p⟩)
  obtain ⟨xl, s', hmtr, hgen, _, _, hpairs, hub_rep, hub_hist⟩ :=
    gossip_propagate_list C hreach allPairs s
  exact ⟨xl, s', hmtr, hgen,
    fun p => le_antisymm
      (hub_rep _ (fun w => Finset.le_sup' s.replica (Finset.mem_univ w)) p)
      (Finset.sup'_le _ _ fun q _ => (hpairs q p (hmem q p)).1),
    fun p => Finset.Subset.antisymm
      (hub_hist _ (fun w => Finset.subset_biUnion_of_mem s.history (Finset.mem_univ w)) p)
      (Finset.biUnion_subset.mpr fun q _ => (hpairs q p (hmem q p)).2)⟩

end CvRDTGossip

/-! ### Operation-based Commutative Replicated Data Types (`CmRDT`) -/

/-- An operation-based **Commutative Replicated Data Type (`CmRDT`)** (after
[ShapiroPreguicaBaqueroZawirski2011], §2.4, pp. 7–8;
[ShapiroPreguicaBaqueroZawirski2011R], §2.2.2 & §2.3.2, pp. 8–11): local updates execute a
side-effect-free `prepare : Op → S → Eff` at the originating replica to produce a downstream
effect payload `Eff`, which is then applied via `effect : Eff → S → S` at all replicas in causal
order. -/
structure CmRDT (S Op Eff Q : Type*) where
  /-- Initial state `s⁰` of every replica. -/
  init : S
  /-- Side-effect-free local query `q : S → Q`. -/
  query : S → Q
  /-- Source-local phase computing the downstream effect payload from `(op, sourceState)`. -/
  prepare : Op → S → Eff
  /-- Downstream state transformer applied at every replica upon delivery. -/
  effect : Eff → S → S

/-- Unconditional downstream commutativity: all effect payloads commute on every state `s`. -/
@[expose]
def EffectsCommute {S Eff : Type*} (effect : Eff → S → S) : Prop :=
  ∀ d₁ d₂ s, effect d₁ (effect d₂ s) = effect d₂ (effect d₁ s)

/-- Concurrent downstream commutativity over an event set `H` with causal precedence `prec`
([ShapiroPreguicaBaqueroZawirski2011], §2.4 Definition 2.6 & Theorem 2.2, p. 8): any two distinct
concurrent events `e₁, e₂ ∈ H` (`¬ prec e₁ e₂` and `¬ prec e₂ e₁`) have commuting downstream
effects. -/
@[expose]
def ConcurrentCommute {S Ev Eff : Type*} (effect : Eff → S → S)
    (prec : Ev → Ev → Prop) (effOf : Ev → Eff) (H : Set Ev) : Prop :=
  ∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → ¬ prec e₁ e₂ → ¬ prec e₂ e₁ →
    ∀ s, effect (effOf e₁) (effect (effOf e₂) s) = effect (effOf e₂) (effect (effOf e₁) s)

theorem EffectsCommute.concurrentCommute {S Ev Eff : Type*} {effect : Eff → S → S}
    (hcomm : EffectsCommute effect) (prec : Ev → Ev → Prop) (effOf : Ev → Eff) (H : Set Ev) :
    ConcurrentCommute effect prec effOf H :=
  fun _ _ _ _ _ _ _ s => hcomm _ _ s

/-- Set `H` is causally closed (downward closed) with respect to causal precedence `prec`. -/
@[expose]
def IsCausallyClosed {Ev : Type*} (prec : Ev → Ev → Prop) (H : Finset Ev) : Prop :=
  ∀ e ∈ H, ∀ e', prec e' e → e' ∈ H

theorem isCausallyClosed_empty {Ev : Type*} (prec : Ev → Ev → Prop) :
    IsCausallyClosed prec (∅ : Finset Ev) :=
  fun _ h => absurd h (Finset.notMem_empty _)

theorem IsCausallyClosed.union {Ev : Type*} [DecidableEq Ev] {prec : Ev → Ev → Prop}
    {H₁ H₂ : Finset Ev} (h₁ : IsCausallyClosed prec H₁) (h₂ : IsCausallyClosed prec H₂) :
    IsCausallyClosed prec (H₁ ∪ H₂) :=
  fun e he e' hprec => (Finset.mem_union.mp he).elim
    (fun he₁ => Finset.mem_union_left H₂ (h₁ e he₁ e' hprec))
    (fun he₂ => Finset.mem_union_right H₁ (h₂ e he₂ e' hprec))

/-- List `l` is a duplicate-free causal linearization of finite event set `H` with respect to
`prec`: `l.Nodup`, `l` has the same elements as `H`, and `prec e₁ e₂` implies `e₁` appears strictly
before `e₂` in `l` (`l.idxOf e₁ < l.idxOf e₂`). -/
@[expose]
def IsCausalLinearization {Ev : Type*} [DecidableEq Ev]
    (prec : Ev → Ev → Prop) (H : Finset Ev) (l : List Ev) : Prop :=
  l.Nodup ∧ (∀ e, e ∈ l ↔ e ∈ H) ∧
    ∀ e₁ ∈ l, ∀ e₂ ∈ l, prec e₁ e₂ → l.idxOf e₁ < l.idxOf e₂

private theorem pairwise_not_prec_of_idxOf_lt {Ev : Type*} [DecidableEq Ev]
    {prec : Ev → Ev → Prop} {l : List Ev} (hnodup : l.Nodup)
    (hord : ∀ e₁ ∈ l, ∀ e₂ ∈ l, prec e₁ e₂ → l.idxOf e₁ < l.idxOf e₂) :
    l.Pairwise (fun a b => ¬ prec b a) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij hprec
  have hlt := hord l[j] (List.getElem_mem hj) l[i] (List.getElem_mem hi) hprec
  rw [hnodup.idxOf_getElem j hj, hnodup.idxOf_getElem i hi] at hlt
  omega

private theorem idxOf_lt_of_pairwise_not_prec {Ev : Type*} [DecidableEq Ev]
    {prec : Ev → Ev → Prop} [Std.Irrefl prec] {l : List Ev}
    (hpw : l.Pairwise (fun a b => ¬ prec b a)) :
    ∀ e₁ ∈ l, ∀ e₂ ∈ l, prec e₁ e₂ → l.idxOf e₁ < l.idxOf e₂ := by
  intro e₁ he₁ e₂ he₂ hprec
  have hi : l.idxOf e₁ < l.length := List.idxOf_lt_length_of_mem he₁
  have hj : l.idxOf e₂ < l.length := List.idxOf_lt_length_of_mem he₂
  rcases lt_trichotomy (l.idxOf e₁) (l.idxOf e₂) with hlt | heq | hgt
  · exact hlt
  · have he₁₂ : e₁ = e₂ := (List.getElem_idxOf hi).symm.trans
      ((by simp [heq] : l[l.idxOf e₁] = l[l.idxOf e₂]).trans (List.getElem_idxOf hj))
    exact absurd (he₁₂ ▸ hprec) (irrefl e₂)
  · exact absurd hprec (by
      simpa [List.getElem_idxOf hi, List.getElem_idxOf hj] using
        List.pairwise_iff_getElem.mp hpw _ _ hj hi hgt)

private theorem foldl_comm_prefix {S Ev Eff : Type*} (effect : Eff → S → S) (effOf : Ev → Eff)
    (a : Ev) (pre : List Ev)
    (hcomm : ∀ x ∈ pre, ∀ s,
      effect (effOf a) (effect (effOf x) s) = effect (effOf x) (effect (effOf a) s))
    (s₀ : S) :
    effect (effOf a) (pre.foldl (fun s e => effect (effOf e) s) s₀) =
      pre.foldl (fun s e => effect (effOf e) s) (effect (effOf a) s₀) := by
  induction pre generalizing s₀ with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← hcomm x List.mem_cons_self s₀]
    exact ih (fun y hy => hcomm y (List.mem_cons_of_mem x hy)) (effect (effOf x) s₀)

private theorem foldl_eq_of_perm_pairwise {S Ev Eff : Type*}
    (effect : Eff → S → S) (prec : Ev → Ev → Prop) (effOf : Ev → Eff) (H : Set Ev)
    (hcomm : ConcurrentCommute effect prec effOf H) :
    ∀ {l₁ l₂ : List Ev},
      l₁.Perm l₂ →
      l₁.Nodup →
      (∀ e ∈ l₁, e ∈ H) →
      l₁.Pairwise (fun a b => ¬ prec b a) →
      l₂.Pairwise (fun a b => ¬ prec b a) →
      ∀ s₀, l₁.foldl (fun s e => effect (effOf e) s) s₀ =
        l₂.foldl (fun s e => effect (effOf e) s) s₀
  | [], l₂, hperm, _, _, _, _, _ => by
      rw [hperm.nil_eq]
  | a :: t₁, l₂, hperm, hnodup₁, hsub₁, hpw₁, hpw₂, s₀ => by
      have hnodup₂ : l₂.Nodup := hperm.nodup_iff.mp hnodup₁
      have ha_mem₂ : a ∈ l₂ := hperm.subset List.mem_cons_self
      obtain ⟨pre, suf, rfl⟩ := List.append_of_mem ha_mem₂
      obtain ⟨ha_not_t₁, hnodup_t₁⟩ := List.nodup_cons.mp hnodup₁
      obtain ⟨hpw_a_t₁, hpw_t₁⟩ := List.pairwise_cons.mp hpw₁
      have hperm_rem : t₁.Perm (pre ++ suf) :=
        (hperm.trans List.perm_middle).cons_inv
      have ha_not_pre : a ∉ pre := fun hmem =>
        (List.nodup_append.mp hnodup₂).2.2 a hmem a List.mem_cons_self rfl
      have hcomm_pre : ∀ x ∈ pre, ∀ s,
          effect (effOf a) (effect (effOf x) s) = effect (effOf x) (effect (effOf a) s) := by
        intro x hx s
        have hx_t₁ : x ∈ t₁ := hperm_rem.symm.subset (List.mem_append_left suf hx)
        have hne : a ≠ x := fun heq => ha_not_pre (heq ▸ hx)
        exact hcomm a (hsub₁ a List.mem_cons_self) x (hsub₁ x (List.mem_cons_of_mem a hx_t₁))
          hne ((List.pairwise_append.mp hpw₂).2.2 x hx a List.mem_cons_self) (hpw_a_t₁ x hx_t₁) s
      have hpw_rem : (pre ++ suf).Pairwise (fun u v => ¬ prec v u) :=
        hpw₂.sublist (List.Sublist.append (List.Sublist.refl pre) (List.sublist_cons_self a suf))
      simp only [List.foldl_cons, List.foldl_append]
      rw [foldl_comm_prefix effect effOf a pre hcomm_pre s₀, ← List.foldl_append]
      exact foldl_eq_of_perm_pairwise effect prec effOf H hcomm hperm_rem hnodup_t₁
        (fun e he => hsub₁ e (List.mem_cons_of_mem a he)) hpw_t₁ hpw_rem (effect (effOf a) s₀)

/-- Op-based Strong Eventual Consistency (`SEC`) strong-convergence step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §2.4 Theorem 2.2, p. 8;
[ShapiroPreguicaBaqueroZawirski2011R], §2.3.2 Proposition 2.2, p. 11): for any finite event set
`H : Finset Ev` whose concurrent events commute under `C.effect`, any two causal linearizations
`l₁` and `l₂` of `H` evaluate from `C.init` to the exact same state. -/
theorem CmRDT.causalLinearization_eq {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) {prec : Ev → Ev → Prop} {effOf : Ev → Eff}
    {H : Finset Ev} {l₁ l₂ : List Ev}
    (hcomm : ConcurrentCommute C.effect prec effOf (H : Set Ev))
    (hl₁ : IsCausalLinearization prec H l₁)
    (hl₂ : IsCausalLinearization prec H l₂) :
    l₁.foldl (fun s e => C.effect (effOf e) s) C.init =
      l₂.foldl (fun s e => C.effect (effOf e) s) C.init := by
  have hperm : l₁.Perm l₂ :=
    (List.perm_ext_iff_of_nodup hl₁.1 hl₂.1).mpr fun e => (hl₁.2.1 e).trans (hl₂.2.1 e).symm
  exact foldl_eq_of_perm_pairwise C.effect prec effOf (H : Set Ev) hcomm hperm hl₁.1
    (fun e he => (hl₁.2.1 e).mp he)
    (pairwise_not_prec_of_idxOf_lt hl₁.1 hl₁.2.2)
    (pairwise_not_prec_of_idxOf_lt hl₂.1 hl₂.2.2)
    C.init

/-! ### Bridge to `Cslib.Distributed.CausalBroadcast` (`CBCAST`) -/

section CausalBroadcastBridge

variable {P S Op Eff Q : Type*} [Fintype P] [DecidableEq P] [DecidableEq Eff]

/-- Replica state of `C : CmRDT S Op Eff Q` at process `q : P` induced by applying `C.effect`
along `q`'s causally delivered packet log `(s.proc q).delivered` in
`Cslib.Distributed.CausalBroadcast.BSSState P Eff`. -/
@[expose]
def CmRDT.bssReplicaState (C : CmRDT S Op Eff Q) (s : BSSState P Eff) (q : P) : S :=
  ((s.proc q).delivered).foldl (fun st pkt => C.effect pkt.payload st) C.init

/-- Every process's `delivered` log in `bssLTS F` forms a causally closed, duplicate-free
`IsCausalLinearization` of `(s.proc q).delivered.toFinset` under `CausalPrec xl`. -/
theorem bss_delivered_isCausalLinearization {F : Set P}
    {xl : List (BSSAction P Eff)} {s : BSSState P Eff}
    (hmtr : (bssLTS F).MTr (bssInit P Eff) xl s) (q : P) :
    IsCausallyClosed (CausalPrec xl) (s.proc q).delivered.toFinset ∧
      IsCausalLinearization (CausalPrec xl) (s.proc q).delivered.toFinset (s.proc q).delivered := by
  refine ⟨?_, bss_no_duplicates hmtr q, fun _ => List.mem_toFinset.symm, ?_⟩
  · intro b₂ hb₂ b₁ hprec
    have hb₂_del : b₂ ∈ (s.proc q).delivered := List.mem_toFinset.mp hb₂
    refine List.mem_toFinset.mpr
      (bss_causal_delivery hmtr ?_ (bss_integrity hmtr q hb₂_del) hprec q hb₂_del).1
    clear hb₂ hb₂_del
    induction hprec with
    | single hstep => exact hstep.elim (fun ⟨i, _, hi, _, _, hbi, _, _⟩ => ⟨i, hi, hbi⟩) And.left
    | tail _ _ ih => exact ih
  · exact fun b₁ hb₁ b₂ hb₂ hprec =>
      (bss_causal_delivery hmtr (bss_integrity hmtr q hb₁) (bss_integrity hmtr q hb₂) hprec q hb₂).2

/-- Causal-broadcast to `CmRDT` strong-convergence bridge step (toward #7502, connecting
`Cslib.Distributed.CausalBroadcast.bssLTS` of [BirmanSchiperStephenson1991], §5.1, directly to
[ShapiroPreguicaBaqueroZawirski2011], §2.4 Theorem 2.2, p. 8): for any static crash-fault set
`F : Set P`, in any finite execution of `bssLTS F`, if concurrent broadcasts in `BroadcastIn xl`
have commuting downstream effects under `C.effect`, then any two processes `p` and `q` (faulty or
correct) that have delivered the same set of packets have identical `CmRDT` states and query
outputs. -/
theorem CmRDT.bss_strong_convergence (C : CmRDT S Op Eff Q) {F : Set P}
    {xl : List (BSSAction P Eff)} {s : BSSState P Eff}
    (hmtr : (bssLTS F).MTr (bssInit P Eff) xl s)
    (hcomm : ConcurrentCommute C.effect (CausalPrec xl) Packet.payload (BroadcastIn xl))
    {p q : P} (hsame : ∀ pkt, pkt ∈ (s.proc p).delivered ↔ pkt ∈ (s.proc q).delivered) :
    C.bssReplicaState s p = C.bssReplicaState s q ∧
      C.query (C.bssReplicaState s p) = C.query (C.bssReplicaState s q) := by
  have hfin_eq : (s.proc p).delivered.toFinset = (s.proc q).delivered.toFinset :=
    Finset.ext fun pkt => by simp [hsame pkt]
  have hcomm_sub : ConcurrentCommute C.effect (CausalPrec xl) Packet.payload
      ((s.proc p).delivered.toFinset : Set (Packet P Eff)) :=
    fun b₁ hb₁ b₂ hb₂ => hcomm b₁ (bss_integrity hmtr p (List.mem_toFinset.mp hb₁))
      b₂ (bss_integrity hmtr p (List.mem_toFinset.mp hb₂))
  have hstate_eq : C.bssReplicaState s p = C.bssReplicaState s q :=
    C.causalLinearization_eq hcomm_sub (bss_delivered_isCausalLinearization hmtr p).2
      (hfin_eq ▸ (bss_delivered_isCausalLinearization hmtr q).2)
  exact ⟨hstate_eq, congrArg C.query hstate_eq⟩

/-- Causal-broadcast to `CmRDT` quiescent eventual-convergence bridge step (toward #7502,
combining `bss_live_of_atomic_multicast` and `CmRDT.bss_strong_convergence`): in any fair infinite
execution `(ss, xs)` of `bssLTS F` with atomic multicast steps (`∀ k, IsAtomicMulticastAction
(xs k)`), if no new broadcasts occur from step `K` onward (`∀ k ≥ K, emittedPacket (ss k) (xs k) =
none`) and concurrent broadcasts commute under `C.effect`, then there exists a convergence step
`M ≥ K` after which all non-crashed replicas `p ∉ F`, `q ∉ F` permanently share identical `CmRDT`
states (`∀ k ≥ M, C.bssReplicaState (ss k) p = C.bssReplicaState (ss k) q`). -/
theorem CmRDT.bss_quiescent_convergence (C : CmRDT S Op Eff Q) {F : Set P}
    {ss : ωSequence (BSSState P Eff)} {xs : ωSequence (BSSAction P Eff)}
    (hinit : ss 0 = bssInit P Eff) (he : (bssLTS F).OmegaExecution ss xs)
    (hfair : BSSFair F ss xs) (hatomic : ∀ k, IsAtomicMulticastAction (xs k))
    {K : ℕ} (hquiesce : ∀ k, K ≤ k → emittedPacket (ss k) (xs k) = none)
    (hcomm : ∀ k, ConcurrentCommute C.effect (CausalPrec (xs.extract 0 k))
      Packet.payload (BroadcastIn (xs.extract 0 k))) :
    ∃ M, K ≤ M ∧ ∀ k, M ≤ k → ∀ p ∉ F, ∀ q ∉ F,
      C.bssReplicaState (ss k) p = C.bssReplicaState (ss k) q := by
  -- For every `(i < K, q)` with `q ∉ F` and an emitted packet at step `i`, liveness yields a
  -- step at which `q` has delivered that packet.
  have hlive_pair : ∀ (idx : Fin K × P), ∃ m : ℕ,
      idx.2 ∉ F → ∀ b, emittedPacket (ss idx.1.val) (xs idx.1.val) = some b →
        b ∈ ((ss m).proc idx.2).delivered := by
    rintro ⟨⟨i, _⟩, q⟩
    by_cases hq : q ∈ F
    · exact ⟨0, fun hq' => absurd hq hq'⟩
    cases hem : emittedPacket (ss i) (xs i) with
    | none => exact ⟨0, fun _ _ h => by cases h⟩
    | some b =>
      obtain ⟨m, hm⟩ := bss_live_of_atomic_multicast hinit he hfair hatomic hq hem
      exact ⟨m, fun _ b' hb' => Option.some.inj hb' ▸ hm⟩
  choose mFn hmFn using hlive_pair
  let M := max K ((Finset.univ : Finset (Fin K × P)).sup mFn)
  refine ⟨M, Nat.le_max_left _ _, fun k hkM p hp q hq => ?_⟩
  have hmtr (n : ℕ) : (bssLTS F).MTr (bssInit P Eff) (xs.extract 0 n) (ss n) :=
    hinit ▸ he.extract_mTr (Nat.zero_le n)
  -- Every broadcast in `xs.extract 0 k` occurred at some step `i < K` (by quiescence from `K`),
  -- hence has already been delivered by step `M ≤ k` at every non-faulty process.
  have hall_deliv : ∀ r : P, r ∉ F → ∀ pkt,
      pkt ∈ ((ss k).proc r).delivered ↔ pkt ∈ BroadcastIn (xs.extract 0 k) := by
    intro r hr pkt
    constructor
    · exact bss_integrity (hmtr k) r
    · rintro ⟨i, hi_len, hbi⟩
      have hi_lt_k : i < k := by
        simpa [ωSequence.length_extract] using hi_len
      have htake : (xs.extract 0 k).take i = xs.extract 0 i := by
        rw [← ωSequence.append_extract_extract (Nat.zero_le i) hi_lt_k.le,
          List.take_left' (by simp [ωSequence.length_extract])]
      have hget : (xs.extract 0 k)[i] = xs i := by
        rw [ωSequence.get_extract (by omega), Nat.zero_add]
      obtain ⟨_, hrun_i⟩ := (bssLTS_mTr_iff F (bssInit P Eff) (xs.extract 0 i) (ss i)).mp (hmtr i)
      have hem_i : emittedPacket (ss i) (xs i) = some pkt := by
        simpa [bssStateAt, htake, ← hrun_i, hget] using hbi
      have hi_lt_K : i < K := not_le.mp fun hge => by simp [hquiesce i hge] at hem_i
      exact bss_omega_delivered_mono he
        ((Finset.le_sup (f := mFn) (Finset.mem_univ (⟨i, hi_lt_K⟩, r))).trans
          ((Nat.le_max_right K _).trans hkM))
        (hmFn (⟨i, hi_lt_K⟩, r) hr pkt hem_i)
  exact (C.bss_strong_convergence (hmtr k) (hcomm k) fun pkt =>
    (hall_deliv p hp pkt).trans (hall_deliv q hq pkt).symm).1

end CausalBroadcastBridge

/-! ### Shapiro et al.'s `CvRDT` ↔ `CmRDT` Emulation Equivalence -/

section Emulation

/-- Operation-based emulation of a state-based `CvRDT` (step toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §3.2.1 Theorem 3.1, p. 9;
[ShapiroPreguicaBaqueroZawirski2011R], §2.4.1 Specification 3, p. 12): `prepare` computes the
post-update state `C.update op s` at the source replica, and `effect` merges received states
downstream via semilattice supremum `(· ⊔ ·)`. -/
@[expose]
def CvRDT.toCmRDT {S Op Q : Type*} [SemilatticeSup S] (C : CvRDT S Op Q) : CmRDT S Op S Q where
  init := C.init
  query := C.query
  prepare := C.update
  effect s' s := s ⊔ s'

/-- State-to-op emulation commutativity step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §3.2.1 Theorem 3.1, p. 9): the downstream merge effects of
`C.toCmRDT` commute unconditionally on every state, requiring not even causal delivery order. -/
theorem CvRDT.toCmRDT_effectsCommute {S Op Q : Type*} [SemilatticeSup S] (C : CvRDT S Op Q) :
    EffectsCommute C.toCmRDT.effect :=
  fun s₁ s₂ s => by simp only [CvRDT.toCmRDT, sup_assoc, sup_comm s₂ s₁]

/-- Executing `prepare` followed immediately by `effect` at the source replica in `C.toCmRDT`
produces the exact same local state `C.update op s` as `C` itself. -/
@[simp]
theorem CvRDT.toCmRDT_source_step {S Op Q : Type*} [SemilatticeSup S]
    (C : CvRDT S Op Q) (op : Op) (s : S) :
    C.toCmRDT.effect (C.toCmRDT.prepare op s) s = C.update op s :=
  sup_eq_right.mpr (C.update_infl op s)

/-- Evaluating `C.toCmRDT` along any event sequence `l` whose set of events is `H` yields the exact
same semilattice state `evalHistory C.init post H` as state-based `C`. -/
theorem CvRDT.toCmRDT_foldl_eq_evalHistory {S Op Q UId : Type*} [SemilatticeSup S]
    (C : CvRDT S Op Q) (post : UId → S) (l : List UId) (H : Finset UId)
    (hmem : ∀ u, u ∈ l ↔ u ∈ H) :
    l.foldl (fun s u => C.toCmRDT.effect (post u) s) C.toCmRDT.init =
      evalHistory C.init post H :=
  foldl_sup_eq_evalHistory C.init post l H hmem

/-- Every nonempty finite set `H : Finset Ev` under a strict partial order `prec` contains a
`prec`-minimal element `m ∈ H` (`∀ y ∈ H, ¬ prec y m`). -/
private theorem exists_minimal_of_nonempty {Ev : Type*}
    (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    {H : Finset Ev} (hne : H.Nonempty) :
    ∃ m ∈ H, ∀ y ∈ H, ¬ prec y m := by
  classical
  -- Choose `m ∈ H` minimizing the cardinality of `{y ∈ H | prec y m}`.
  let ancCard : Ev → ℕ := fun x => (H.filter (fun y => prec y x)).card
  obtain ⟨m, hmH, hmin⟩ := H.exists_min_image ancCard hne
  refine ⟨m, hmH, fun y hyH hprec => not_lt_of_ge (hmin y hyH) (Finset.card_lt_card ?_)⟩
  exact Finset.ssubset_iff_of_subset
    (fun z hz => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1, _root_.trans (Finset.mem_filter.mp hz).2 hprec⟩) |>.mpr
    ⟨y, Finset.mem_filter.mpr ⟨hyH, hprec⟩, fun hy => irrefl y (Finset.mem_filter.mp hy).2⟩

/-- Every finite event set `H : Finset Ev` equipped with a strict partial order `prec` admits a
causal linearization `l : List Ev` (`IsCausalLinearization prec H l`). -/
theorem exists_causalLinearization {Ev : Type*} [DecidableEq Ev]
    (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec] (H : Finset Ev) :
    ∃ l : List Ev, IsCausalLinearization prec H l := by
  induction H using Finset.strongInduction with
  | H H ih =>
    rcases H.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, by simp⟩
    obtain ⟨m, hmH, hmin⟩ := exists_minimal_of_nonempty prec hne
    obtain ⟨tl, htl_nodup, htl_mem, htl_ord⟩ := ih (H.erase m) (Finset.erase_ssubset hmH)
    have hmem_cons : ∀ e, e ∈ m :: tl ↔ e ∈ H := fun e => by
      rw [List.mem_cons, htl_mem, ← Finset.mem_insert, Finset.insert_erase hmH]
    have hpw_cons : (m :: tl).Pairwise (fun a b => ¬ prec b a) :=
      List.pairwise_cons.mpr ⟨fun b hb => hmin b ((hmem_cons b).mp (List.mem_cons_of_mem m hb)),
        pairwise_not_prec_of_idxOf_lt htl_nodup htl_ord⟩
    exact ⟨m :: tl, List.nodup_cons.mpr ⟨fun hm => (Finset.mem_erase.mp ((htl_mem m).mp hm)).1 rfl,
      htl_nodup⟩, hmem_cons, idxOf_lt_of_pairwise_not_prec hpw_cons⟩

/-- Evaluate `C : CmRDT S Op Eff Q` on a finite event set `H : Finset Ev` ordered by strict
partial order `prec` via causal linearization ([ShapiroPreguicaBaqueroZawirski2011], §3.2.2
Theorem 3.2, pp. 9–10). Under `ConcurrentCommute`, `CmRDT.evalCausalSet_eq_foldl` proves this value
is independent of the chosen causal linearization. -/
noncomputable def CmRDT.evalCausalSet {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (effOf : Ev → Eff) (H : Finset Ev) : S :=
  (Classical.choose (exists_causalLinearization prec H)).foldl
    (fun s e => C.effect (effOf e) s) C.init

/-- Under `ConcurrentCommute`, `C.evalCausalSet prec effOf H` agrees with folding `C.effect` over
any causal linearization `l` of `H`. -/
theorem CmRDT.evalCausalSet_eq_foldl {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (effOf : Ev → Eff) {H : Finset Ev} {l : List Ev}
    (hcomm : ConcurrentCommute C.effect prec effOf (H : Set Ev))
    (hl : IsCausalLinearization prec H l) :
    C.evalCausalSet prec effOf H = l.foldl (fun s e => C.effect (effOf e) s) C.init :=
  C.causalLinearization_eq hcomm (Classical.choose_spec (exists_causalLinearization prec H)) hl

@[simp]
theorem CmRDT.evalCausalSet_empty {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (effOf : Ev → Eff) :
    C.evalCausalSet prec effOf (∅ : Finset Ev) = C.init :=
  C.evalCausalSet_eq_foldl prec effOf (fun _ h => by simp at h)
    ⟨List.nodup_nil, by simp, by simp⟩

/-- Adding a fresh causally maximal event `e ∉ H` (`∀ x ∈ H, ¬ prec e x`) advances
`C.evalCausalSet` by applying `C.effect (effOf e)` directly to `C.evalCausalSet prec effOf H`. -/
theorem CmRDT.evalCausalSet_insert_max {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (effOf : Ev → Eff) {H : Finset Ev} {e : Ev} (he_not : e ∉ H)
    (hmax : ∀ x ∈ H, ¬ prec e x)
    (hcomm : ConcurrentCommute C.effect prec effOf ((insert e H : Finset Ev) : Set Ev)) :
    C.evalCausalSet prec effOf (insert e H) =
      C.effect (effOf e) (C.evalCausalSet prec effOf H) := by
  obtain ⟨l, hl⟩ := exists_causalLinearization prec H
  have he_not_l : e ∉ l := fun h => he_not ((hl.2.1 e).mp h)
  have hnodup_app : (l ++ [e]).Nodup :=
    List.nodup_append.mpr ⟨hl.1, List.nodup_singleton e,
      fun _ hx _ hy hxy => he_not_l (List.mem_singleton.mp hy ▸ (hxy ▸ hx))⟩
  have hpw_app : (l ++ [e]).Pairwise (fun a b => ¬ prec b a) :=
    List.pairwise_append.mpr ⟨pairwise_not_prec_of_idxOf_lt hl.1 hl.2.2,
      List.pairwise_singleton _ e,
      fun x hx _ hy => List.mem_singleton.mp hy ▸ hmax x ((hl.2.1 x).mp hx)⟩
  have hlin_app : IsCausalLinearization prec (insert e H) (l ++ [e]) := by
    refine ⟨hnodup_app, fun x => ?_, idxOf_lt_of_pairwise_not_prec hpw_app⟩
    rw [List.mem_append, List.mem_singleton, hl.2.1 x, Finset.mem_insert]
    exact or_comm
  have hcomm_H : ConcurrentCommute C.effect prec effOf (H : Set Ev) :=
    fun x hx y hy => hcomm x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)
  rw [C.evalCausalSet_eq_foldl prec effOf hcomm hlin_app, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ← C.evalCausalSet_eq_foldl prec effOf hcomm_H hl]

/-- Iterated causal-readiness step starting from `∅`: after `n` rounds against known-event pool
`M` and explicit dependency map `deps : Ev → Finset Ev`, returns the subset of events in `M` whose
transitive `deps` chains of depth `< n` all lie inside `M` ([ShapiroPreguicaBaqueroZawirski2011],
§3.2.2 Theorem 3.2, pp. 9–10; [ShapiroPreguicaBaqueroZawirski2011R], §2.4.2 Specification 4,
p. 13). -/
@[expose]
def deliverableIter {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) : ℕ → Finset Ev
  | 0 => ∅
  | n + 1 =>
      let D := deliverableIter deps M n
      D ∪ M.filter (fun e => deps e ⊆ D)

/-- Maximal `deps`-closed subset `D ⊆ M` of causally deliverable events in `M`, computed in
`M.card` iterations of `deliverableIter`. -/
@[expose]
def deliverableEvents {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) : Finset Ev :=
  deliverableIter deps M M.card

private theorem deliverableIter_subset {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) : ∀ n, deliverableIter deps M n ⊆ M
  | 0 => Finset.empty_subset M
  | n + 1 => Finset.union_subset (deliverableIter_subset deps M n) (Finset.filter_subset _ M)

private theorem deliverableIter_step_mono {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) (n : ℕ) : deliverableIter deps M n ⊆ deliverableIter deps M (n + 1) :=
  Finset.subset_union_left

private theorem deliverableIter_mono_nat {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) {m n : ℕ} (hmn : m ≤ n) :
    deliverableIter deps M m ⊆ deliverableIter deps M n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    exact Finset.Subset.trans (ih (Nat.le_add_right m k)) (deliverableIter_step_mono deps M (m + k))

private theorem deliverableIter_mono_pool {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    {M₁ M₂ : Finset Ev} (hM : M₁ ⊆ M₂) :
    ∀ n, deliverableIter deps M₁ n ⊆ deliverableIter deps M₂ n
  | 0 => Finset.Subset.refl _
  | n + 1 => Finset.union_subset_union (deliverableIter_mono_pool deps hM n) fun _ he =>
    Finset.mem_filter.mpr ⟨hM (Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2.trans (deliverableIter_mono_pool deps hM n)⟩

theorem deliverableEvents_subset {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    (M : Finset Ev) : deliverableEvents deps M ⊆ M :=
  deliverableIter_subset deps M M.card

/-- Monotonicity of `deliverableEvents`: growing the known-event pool `M₁ ⊆ M₂` monotonically
grows the causally deliverable subset. -/
theorem deliverableEvents_mono {Ev : Type*} [DecidableEq Ev] (deps : Ev → Finset Ev)
    {M₁ M₂ : Finset Ev} (hM : M₁ ⊆ M₂) :
    deliverableEvents deps M₁ ⊆ deliverableEvents deps M₂ :=
  Finset.Subset.trans
    (deliverableIter_mono_pool deps hM M₁.card)
    (deliverableIter_mono_nat deps M₂ (Finset.card_le_card hM))

/-- When `M` is already closed under `deps` (`∀ e ∈ M, deps e ⊆ M`) and `prec` is a strict partial
order with `∀ e x, x ∈ deps e → prec x e`, every event in `M` becomes causally deliverable within
`M.card` steps (`deliverableEvents deps M = M`). -/
theorem deliverableEvents_eq_self_of_closed {Ev : Type*} [DecidableEq Ev]
    (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (deps : Ev → Finset Ev) (hdeps_prec : ∀ e x, x ∈ deps e → prec x e)
    {M : Finset Ev} (hclosed : ∀ e ∈ M, deps e ⊆ M) :
    deliverableEvents deps M = M := by
  apply Finset.Subset.antisymm (deliverableEvents_subset deps M)
  by_contra hnot_sub
  -- Otherwise at each step `k < M.card`, `M \ deliverableIter deps M k` is nonempty, so picking a
  -- `prec`-minimal element in `M \ D_k` strictly increases `(deliverableIter deps M k).card`.
  have hcard_ge : ∀ k ≤ M.card, k ≤ (deliverableIter deps M k).card := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      set D := deliverableIter deps M k
      have hnot_D : ¬ M ⊆ D := fun hsub =>
        hnot_sub (Finset.Subset.trans hsub (deliverableIter_mono_nat deps M (Nat.le_of_succ_le hk)))
      obtain ⟨m, hm_sdiff, hm_min⟩ :=
        exists_minimal_of_nonempty prec (Finset.sdiff_nonempty.mpr hnot_D)
      obtain ⟨hmM, hmNotD⟩ := Finset.mem_sdiff.mp hm_sdiff
      have hm_in_next : m ∈ deliverableIter deps M (k + 1) :=
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmM, fun y hy => by
          by_contra hyNotD
          exact hm_min y (Finset.mem_sdiff.mpr ⟨hclosed m hmM hy, hyNotD⟩) (hdeps_prec m y hy)⟩)
      exact Nat.succ_le_of_lt ((ih (Nat.le_of_succ_le hk)).trans_lt (Finset.card_lt_card
        ((Finset.ssubset_iff_of_subset (deliverableIter_step_mono deps M k)).mpr
          ⟨m, hm_in_next, hmNotD⟩)))
  have hge_full : M.card ≤ (deliverableEvents deps M).card := hcard_ge M.card le_rfl
  exact hnot_sub (Finset.eq_of_subset_of_card_le (deliverableEvents_subset deps M) hge_full).ge

/-- State-based `CvRDT` emulation of an operation-based `CmRDT` (step toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011], §3.2.2 Theorem 3.2, pp. 9–10;
[ShapiroPreguicaBaqueroZawirski2011R], §2.4.2 Specification 4, p. 13): replicas maintain known
unique events `M : Finset Ev` ordered by `(⊆)` with merge `(· ∪ ·)`, update locally by inserting a
newly generated event `insert e M`, and answer queries by evaluating `C` over the causally
deliverable subset `deliverableEvents deps M`. -/
noncomputable def CmRDT.toCvRDT {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (deps : Ev → Finset Ev) (effOf : Ev → Eff) :
    CvRDT (Finset Ev) Ev Q where
  init := ∅
  query M := C.query (C.evalCausalSet prec effOf (deliverableEvents deps M))
  update e M := insert e M
  update_infl e M := Finset.subset_insert e M

/-- On any `deps`-closed known-event history `M` whose concurrent events commute, the state-based
emulation `(C.toCvRDT prec deps effOf).query M` returns the exact same query result as applying `C`
along any causal linearization `l` of `M`. -/
theorem CmRDT.toCvRDT_query_eq {S Op Eff Q Ev : Type*} [DecidableEq Ev]
    (C : CmRDT S Op Eff Q) (prec : Ev → Ev → Prop) [IsStrictOrder Ev prec]
    (deps : Ev → Finset Ev) (hdeps_prec : ∀ e x, x ∈ deps e → prec x e)
    (effOf : Ev → Eff) {M : Finset Ev} (hclosed : ∀ e ∈ M, deps e ⊆ M)
    {l : List Ev} (hcomm : ConcurrentCommute C.effect prec effOf (M : Set Ev))
    (hl : IsCausalLinearization prec M l) :
    (C.toCvRDT prec deps effOf).query M =
      C.query (l.foldl (fun s e => C.effect (effOf e) s) C.init) := by
  simp only [CmRDT.toCvRDT, deliverableEvents_eq_self_of_closed prec deps hdeps_prec hclosed]
  exact congrArg C.query (C.evalCausalSet_eq_foldl prec effOf hcomm hl)

end Emulation

end Cslib.Distributed.CRDT
