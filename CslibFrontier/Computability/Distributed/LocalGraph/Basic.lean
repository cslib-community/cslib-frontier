/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ProperColoring
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Image

/-!
# General-Graph Synchronous `LOCAL` Model and Covering-Map Impossibility

Deterministic synchronous message-passing protocols on general locally finite simple graphs
`G : SimpleGraph V` in both the broadcast/multiset `LOCAL` variant (`BroadcastProtocol`) and the
port-numbered `LOCAL` (`PN` + local inputs) variant (`PortNumbering`, `PortProtocol`), together
with covering-map fiber invariance and anonymous symmetry-breaking impossibility steps towards
`#7505` (after [Angluin][Angluin1980b] and [Hirvonen and Suomela][HirvonenSuomela2020], Chapters 3,
4, and 7).

**Model scope and relationship to `[Angluin1980b]`:**
In [Hirvonen and Suomela][HirvonenSuomela2020] (§3.2–3.3, pp. 39–45; §7.1–7.2, Theorem 7.1,
pp. 115–119), port-numbered networks allow self-loops and parallel edges. Here protocols execute
directly over Mathlib's loopless `SimpleGraph V` (`[G.LocallyFinite]`), while asynchronous
processor-network schedules from `[Angluin1980b]` remain open under `#7505`. Every
`BroadcastProtocol` embeds into `PortProtocol` with identical round-by-round states
(`BroadcastProtocol.toPortProtocol_state`), and every `PortCovering` induces a
neighborhood-bijective `GraphCovering` (`PortCovering.toGraphCovering`).

## Main definitions

* `Cslib.Distributed.LocalGraph.BroadcastProtocol`: synchronous broadcast/multiset message-passing
  `LOCAL` protocol on `SimpleGraph V`, with `fullInfo`, `state`, `run`, and `seq`.
* `Cslib.Distributed.LocalGraph.PortNumbering`, `PortProtocol`: port assignments
  `G.neighborSet u ≃ Fin (G.degree u)` and synchronous port-numbered `LOCAL` protocols, with
  `state`, `run`, and `BroadcastProtocol.toPortProtocol`.
* `Cslib.Distributed.LocalGraph.GraphCovering`, `PortCovering`: surjective graph covering maps
  bijective on neighborhoods and port-preserving covering maps.
* `Cslib.Distributed.LocalGraph.ElectsUniqueLeader`: unique-leader output predicate `∃! u, f u`.
* `Cslib.Distributed.LocalGraph.bipartiteDoubleCover`: Kronecker double cover `G × K₂` on
  `Bool × V`, together with `PortNumbering.bipartiteDoubleCover`.
* `Cslib.Distributed.LocalGraph.cycleDoubleCoverMap`, `cycleGraphPortNumbering`: canonical 2-fold
  covering `C₆ → C₃` on `SimpleGraph.cycleGraph` and oriented cycle port numberings.
* `Cslib.Distributed.LocalGraph.k33PortNumbering`: symmetric port numbering on
  `completeBipartiteGraph (Fin 3) (Fin 3)`.

## Main results

* `Cslib.Distributed.LocalGraph.BroadcastProtocol.state_eq_of_graphCovering`: fiber state
  invariance under surjective neighborhood-bijective graph coverings across all rounds `r : ℕ`.
* `Cslib.Distributed.LocalGraph.PortProtocol.state_eq_of_portCovering`: fiber state invariance
  under port-preserving coverings across all rounds `r : ℕ` (simple-graph synchronous step after
  Theorem 7.1 of `[HirvonenSuomela2020]` and `[Angluin1980b]`).
* `Cslib.Distributed.LocalGraph.PortProtocol.not_electsUniqueLeader_of_portCovering`,
  `BroadcastProtocol.not_electsUniqueLeader_of_graphCovering`: impossibility of deterministic
  anonymous leader election whenever every base vertex has at least two distinct fiber preimages.
* `Cslib.Distributed.LocalGraph.PortProtocol.not_isProperColoring_of_portCovering`,
  `BroadcastProtocol.not_isProperColoring_of_graphCovering`: if `¬ G₂.Colorable q`, no
  deterministic anonymous protocol properly `q`-colors a cover `G₁` of `G₂`.
* `Cslib.Distributed.LocalGraph.bipartiteDoubleCover_colorable_two`,
  `PortProtocol.not_electsUniqueLeader_bipartiteDoubleCover`,
  `PortProtocol.not_isProperColoring_bipartiteDoubleCover`: every bipartite double cover is
  2-colorable, yet under `N.bipartiteDoubleCover` admits neither anonymous leader election nor
  anonymous `q`-coloring when `¬ G.Colorable q`.
* `Cslib.Distributed.LocalGraph.cycleGraph_six_colorable_two`,
  `not_cycleGraph_three_colorable_two`,
  `BroadcastProtocol.not_electsUniqueLeader_cycleGraph_six`,
  `BroadcastProtocol.not_twoColoring_cycleGraph_six`,
  `PortProtocol.not_electsUniqueLeader_cycleGraphPortNumbering_six`,
  `PortProtocol.not_twoColoring_cycleGraphPortNumbering_six`: `C₆` is 2-colorable (`χ(C₆) = 2`),
  `C₃` is not (`χ(C₃) = 3`), and lifting `C₆ → C₃` rules out anonymous leader election and
  anonymous 2-coloring for all `BroadcastProtocol`s and for `PortProtocol`s under
  `cycleGraphPortNumbering 3`.
* `Cslib.Distributed.LocalGraph.PortProtocol.state_k33PortNumbering_eq`,
  `PortProtocol.not_electsUniqueLeader_k33PortNumbering`,
  `PortProtocol.not_isProperColoring_k33PortNumbering`: under `k33PortNumbering`, all six vertices
  of `K₃,₃` share identical states in every round, ruling out anonymous leader election and proper
  coloring.

## References

* [D. Angluin, *Local and Global Properties in Networks of Processors*][Angluin1980b]
* [J. Hirvonen and J. Suomela, *Distributed Algorithms 2020*][HirvonenSuomela2020], Chapters 3, 4,
  and 7
-/

public section

namespace Cslib.Distributed.LocalGraph

/-! ### Broadcast `LOCAL` protocols on `SimpleGraph` -/

/-- A deterministic synchronous broadcast `LOCAL` protocol on simple graphs.

Each node initializes its local state from its input via `init`. In round `r`, every node in state
`s` broadcasts `send r s` to all of its neighbors and updates its state via `recv r s msgs`, where
`msgs` is the multiset of messages received from its neighbors. After the final round each node
outputs `output s`. -/
structure BroadcastProtocol (I S M O : Type*) where
  /-- Initial local state from a node's input. -/
  init : I → S
  /-- Message broadcast to all neighbors in round `r`. -/
  send : ℕ → S → M
  /-- State transition after round `r` from own state and multiset of neighbor messages. -/
  recv : ℕ → S → Multiset M → S
  /-- Output computed from a local state. -/
  output : S → O

namespace BroadcastProtocol

/-- A full-information (state-exchange) broadcast `LOCAL` protocol in which nodes broadcast their
entire local state `S` in every round. -/
@[expose] def fullInfo {I S O : Type*} (init : I → S) (step : ℕ → S → Multiset S → S)
    (output : S → O) : BroadcastProtocol I S S O where
  init := init
  send _ s := s
  recv := step
  output := output

section Exec

variable {V I S M O : Type*} (P : BroadcastProtocol I S M O)
  (G : SimpleGraph V) [G.LocallyFinite]

/-- Local state of node `u` after `r` synchronous rounds of `P` on graph `G` with inputs `x`. -/
@[expose] def state (x : V → I) : ℕ → V → S
  | 0, u => P.init (x u)
  | r + 1, u =>
    P.recv r (state x r u) ((G.neighborFinset u).val.map fun w => P.send r (state x r w))

/-- Output of node `u` after `r` synchronous rounds of `P` on graph `G` with inputs `x`. -/
@[expose] def run (x : V → I) (r : ℕ) (u : V) : O :=
  P.output (P.state G x r u)

@[simp] theorem state_zero (x : V → I) (u : V) : P.state G x 0 u = P.init (x u) := rfl

theorem state_succ (x : V → I) (r : ℕ) (u : V) :
    P.state G x (r + 1) u =
      P.recv r (P.state G x r u)
        ((G.neighborFinset u).val.map fun w => P.send r (P.state G x r w)) := rfl

/-- Post-process the output of a `BroadcastProtocol` by `g`. -/
@[expose] def mapOutput {O' : Type*} (g : O → O') : BroadcastProtocol I S M O' where
  init := P.init
  send := P.send
  recv := P.recv
  output := g ∘ P.output

private theorem state_eq_of_init_send_recv {I' O' : Type*} {Q : BroadcastProtocol I' S M O'}
    {x' : V → I'} {x : V → I} (hi : ∀ u, Q.init (x' u) = P.init (x u))
    (hs : Q.send = P.send) (hr : Q.recv = P.recv) (r : ℕ) :
    Q.state G x' r = P.state G x r := by
  funext u
  induction r generalizing u with
  | zero => exact hi u
  | succ r ih =>
    rw [state_succ, state_succ, hr, hs, ih u]
    congr 1
    exact Multiset.map_congr rfl fun w _ => by rw [ih w]

@[simp] theorem mapOutput_state {O' : Type*} (g : O → O') (x : V → I) (r : ℕ) :
    (P.mapOutput g).state G x r = P.state G x r :=
  state_eq_of_init_send_recv P G (Q := P.mapOutput g) (fun _ => rfl) rfl rfl r

@[simp] theorem mapOutput_run {O' : Type*} (g : O → O') (x : V → I) (r : ℕ) (u : V) :
    (P.mapOutput g).run G x r u = g (P.run G x r u) := by
  rw [run, mapOutput_state]
  rfl

/-- Pre-process the input of a `BroadcastProtocol` by `f`. -/
@[expose] def comapInput {I' : Type*} (f : I' → I) : BroadcastProtocol I' S M O where
  init := P.init ∘ f
  send := P.send
  recv := P.recv
  output := P.output

@[simp] theorem comapInput_state {I' : Type*} (f : I' → I) (x : V → I') (r : ℕ) :
    (P.comapInput f).state G x r = P.state G (f ∘ x) r :=
  state_eq_of_init_send_recv P G (Q := P.comapInput f) (fun _ => rfl) rfl rfl r

@[simp] theorem comapInput_run {I' : Type*} (f : I' → I) (x : V → I') (r : ℕ) (u : V) :
    (P.comapInput f).run G x r u = P.run G (f ∘ x) r u := by
  rw [run, comapInput_state]
  rfl

end Exec

section Seq

variable {V I S₁ M₁ O₁ S₂ M₂ O₂ : Type*}

/-- Sequential composition of broadcast protocols: run `A` for `t` rounds, then run `B` on the
round-`t` outputs of `A`. -/
@[expose] def seq (A : BroadcastProtocol I S₁ M₁ O₁) (t : ℕ)
    (B : BroadcastProtocol O₁ S₂ M₂ O₂) :
    BroadcastProtocol I (S₁ × S₂) (M₁ ⊕ M₂) O₂ where
  init x :=
    let s₁ := A.init x
    (s₁, B.init (A.output s₁))
  send k p :=
    if k < t then Sum.inl (A.send k p.1) else Sum.inr (B.send (k - t) p.2)
  recv k p ms :=
    if k < t then
      let s₁' := A.recv k p.1 (ms.filterMap Sum.getLeft?)
      (s₁', B.init (A.output s₁'))
    else
      (p.1, B.recv (k - t) p.2 (ms.filterMap Sum.getRight?))
  output p := B.output p.2

private theorem filterMap_getLeft_map_inl {α β γ : Type*} (s : Multiset α) (f : α → β) :
    (s.map fun a => (Sum.inl (f a) : β ⊕ γ)).filterMap Sum.getLeft? = s.map f :=
  (Multiset.filterMap_map _ _ s).trans (congrFun (Multiset.filterMap_eq_map f) s)

private theorem filterMap_getRight_map_inr {α β γ : Type*} (s : Multiset α) (f : α → γ) :
    (s.map fun a => (Sum.inr (f a) : β ⊕ γ)).filterMap Sum.getRight? = s.map f :=
  (Multiset.filterMap_map _ _ s).trans (congrFun (Multiset.filterMap_eq_map f) s)

private theorem seq_state_le (A : BroadcastProtocol I S₁ M₁ O₁) {t : ℕ}
    (B : BroadcastProtocol O₁ S₂ M₂ O₂) (G : SimpleGraph V) [G.LocallyFinite] (x : V → I)
    {s : ℕ} (hs : s ≤ t) (u : V) :
    (A.seq t B).state G x s u =
      (A.state G x s u, B.init (A.output (A.state G x s u))) := by
  induction s generalizing u with
  | zero => rfl
  | succ s ih =>
    have hlt : s < t := by omega
    have hmap :
        ((G.neighborFinset u).val.map fun w =>
          (A.seq t B).send s ((A.seq t B).state G x s w)).filterMap Sum.getLeft? =
        (G.neighborFinset u).val.map fun w => A.send s (A.state G x s w) := by
      have hsend : (fun w => (A.seq t B).send s ((A.seq t B).state G x s w)) =
          fun w => (Sum.inl (A.send s (A.state G x s w)) : M₁ ⊕ M₂) := by
        funext w
        rw [ih (by omega) w]
        simp only [seq, hlt, ↓reduceIte]
      rw [hsend, filterMap_getLeft_map_inl]
    rw [state_succ, ih (by omega) u]
    change (if s < t then
        let s₁' := A.recv s (A.state G x s u)
          (((G.neighborFinset u).val.map fun w =>
            (A.seq t B).send s ((A.seq t B).state G x s w)).filterMap Sum.getLeft?)
        (s₁', B.init (A.output s₁'))
      else _) = _
    simp only [hlt, ↓reduceIte, hmap, ← state_succ]

/-- Running `A.seq t B` for `t + r` rounds equals running `B` for `r` rounds on `A.run G x t`. -/
theorem seq_run (A : BroadcastProtocol I S₁ M₁ O₁) (t : ℕ)
    (B : BroadcastProtocol O₁ S₂ M₂ O₂) (G : SimpleGraph V) [G.LocallyFinite] (x : V → I)
    (r : ℕ) (u : V) :
    (A.seq t B).run G x (t + r) u = B.run G (A.run G x t) r u := by
  suffices h : ∀ v, (A.seq t B).state G x (t + r) v =
      (A.state G x t v, B.state G (A.run G x t) r v) from
    congrArg (B.output ∘ Prod.snd) (h u)
  induction r with
  | zero =>
    intro v
    rw [Nat.add_zero, seq_state_le A B G x le_rfl v]
    rfl
  | succ r ih =>
    intro v
    have hlt : ¬ t + r < t := by omega
    have hmap :
        ((G.neighborFinset v).val.map fun w =>
          (A.seq t B).send (t + r) ((A.seq t B).state G x (t + r) w)).filterMap Sum.getRight? =
        (G.neighborFinset v).val.map fun w => B.send r (B.state G (A.run G x t) r w) := by
      have hsend : (fun w => (A.seq t B).send (t + r) ((A.seq t B).state G x (t + r) w)) =
          fun w => (Sum.inr (B.send r (B.state G (A.run G x t) r w)) : M₁ ⊕ M₂) := by
        funext w
        rw [ih w]
        simp only [seq, hlt, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [hsend, filterMap_getRight_map_inr]
    rw [← Nat.add_assoc, state_succ, ih v]
    change (if t + r < t then _ else
      (A.state G x t v, B.recv (t + r - t) (B.state G (A.run G x t) r v)
        (((G.neighborFinset v).val.map fun w =>
          (A.seq t B).send (t + r) ((A.seq t B).state G x (t + r) w)).filterMap
            Sum.getRight?))) = _
    simp only [hlt, ↓reduceIte, Nat.add_sub_cancel_left, hmap, ← state_succ]

end Seq

end BroadcastProtocol

/-! ### Port-numbered `LOCAL` networks and protocols -/

/-- A port numbering of a locally finite simple graph `G`: at each vertex `u`, a bijection between
its neighborhood `G.neighborSet u` and its local port indices `Fin (G.degree u)`. -/
structure PortNumbering {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] where
  /-- Local port bijection at vertex `u`. -/
  port : ∀ u : V, G.neighborSet u ≃ Fin (G.degree u)

/-- A deterministic synchronous port-numbered `LOCAL` protocol (`PN` algorithm with local inputs,
[Hirvonen and Suomela][HirvonenSuomela2020], §3.3 and §4.1).

Each node of degree `d` initializes its state via `init d (x u)`. In round `r`, a node of degree
`d` in state `s` sends `send r d s p` out each port `p : Fin d`, receives `incoming : Fin d → M`
along its incident ports, and updates to `recv r d s incoming`. -/
structure PortProtocol (I S M O : Type*) where
  /-- Initial state of a degree-`d` node with local input `x`. -/
  init : ℕ → I → S
  /-- Message sent in round `r` out port `p` by a degree-`d` node in state `s`. -/
  send : ℕ → (d : ℕ) → S → Fin d → M
  /-- Next state after round `r` of a degree-`d` node from own state and port-indexed messages. -/
  recv : ℕ → (d : ℕ) → S → (Fin d → M) → S
  /-- Output computed from a local state. -/
  output : S → O

namespace PortProtocol

variable {V I S M O : Type*} (P : PortProtocol I S M O)
  {G : SimpleGraph V} [G.LocallyFinite] (N : PortNumbering G)

/-- Local state of node `u` after `r` synchronous rounds on the port-numbered network `N`. -/
@[expose] def state (x : V → I) : ℕ → V → S
  | 0, u => P.init (G.degree u) (x u)
  | r + 1, u =>
    P.recv r (G.degree u) (state x r u) fun i =>
      let w := (N.port u).symm i
      P.send r (G.degree w.1) (state x r w.1) (N.port w.1 ⟨u, w.2.symm⟩)

/-- Output of node `u` after `r` synchronous rounds on the port-numbered network `N`. -/
@[expose] def run (x : V → I) (r : ℕ) (u : V) : O :=
  P.output (P.state N x r u)

@[simp] theorem state_zero (x : V → I) (u : V) :
    P.state N x 0 u = P.init (G.degree u) (x u) := rfl

theorem state_succ (x : V → I) (r : ℕ) (u : V) :
    P.state N x (r + 1) u =
      P.recv r (G.degree u) (P.state N x r u) fun i =>
        let w := (N.port u).symm i
        P.send r (G.degree w.1) (P.state N x r w.1) (N.port w.1 ⟨u, w.2.symm⟩) := rfl

end PortProtocol

namespace BroadcastProtocol

variable {V I S M O : Type*} (P : BroadcastProtocol I S M O)

/-- View a `BroadcastProtocol` as a `PortProtocol` that sends the same message on every outgoing
port and aggregates incoming port messages as a `Multiset`. -/
@[expose] def toPortProtocol : PortProtocol I S M O where
  init _ x := P.init x
  send r _ s _ := P.send r s
  recv r _ s incoming := P.recv r s (Finset.univ.val.map incoming)
  output := P.output

/-- Simulating a `BroadcastProtocol` on any port numbering of `G` goes through the exact same
states in every round. -/
theorem toPortProtocol_state {G : SimpleGraph V} [G.LocallyFinite] (N : PortNumbering G)
    (x : V → I) (r : ℕ) (u : V) :
    P.toPortProtocol.state N x r u = P.state G x r u := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    have hrecv : ∀ d s inc,
        P.toPortProtocol.recv r d s inc = P.recv r s (Finset.univ.val.map inc) :=
      fun _ _ _ => rfl
    have hsend : ∀ d s p, P.toPortProtocol.send r d s p = P.send r s := fun _ _ _ => rfl
    rw [PortProtocol.state_succ, hrecv, state_succ, ih u]
    congr 1
    let e : G.neighborFinset u ≃ Fin (G.degree u) :=
      (Equiv.subtypeEquivRight fun w => G.mem_neighborFinset u w).trans (N.port u)
    have huniv : (Finset.univ : Finset (Fin (G.degree u))).val =
        (Finset.univ : Finset (G.neighborFinset u)).val.map e := by
      have hm := congrArg Finset.val (Finset.map_univ_equiv e).symm
      simpa only [Finset.map_val, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding] using hm
    rw [huniv, Multiset.map_map]
    have hcomp :
        ((fun i : Fin (G.degree u) =>
          P.toPortProtocol.send r (G.degree ((N.port u).symm i).1)
            (P.toPortProtocol.state N x r ((N.port u).symm i).1)
            (N.port ((N.port u).symm i).1 ⟨u, ((N.port u).symm i).2.symm⟩)) ∘ e) =
        fun w : G.neighborFinset u => P.send r (P.state G x r w.1) := by
      funext w
      dsimp only [Function.comp_apply]
      rw [hsend]
      have hw : (N.port u).symm (e w) = ⟨w.1, (G.mem_neighborFinset u w.1).1 w.2⟩ :=
        (N.port u).symm_apply_apply _
      have hw1 : ((N.port u).symm (e w)).1 = w.1 := congrArg Subtype.val hw
      rw [hw1, ih w.1]
    rw [hcomp, Finset.univ_eq_attach,
      show (fun w : {x // x ∈ G.neighborFinset u} => P.send r (P.state G x r w.1)) =
        (fun w => P.send r (P.state G x r w)) ∘ Subtype.val from rfl,
      ← Multiset.map_map, Finset.attach_val, Multiset.attach_map_val]

@[simp] theorem toPortProtocol_run {G : SimpleGraph V} [G.LocallyFinite] (N : PortNumbering G)
    (x : V → I) (r : ℕ) (u : V) :
    P.toPortProtocol.run N x r u = P.run G x r u := by
  rw [PortProtocol.run, toPortProtocol_state]
  rfl

end BroadcastProtocol

/-! ### Covering maps and Angluin fiber state invariance -/

/-- A surjective graph covering map `φ : V₁ → V₂` from `G₁` to `G₂`: `φ` is surjective, preserves
adjacency, and maps `G₁.neighborSet u` bijectively onto `G₂.neighborSet (φ u)` for every vertex
`u : V₁`. -/
structure GraphCovering {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    (φ : V₁ → V₂) : Prop where
  /-- Every vertex of `G₂` lies in the image of `φ`. -/
  surjective : Function.Surjective φ
  /-- `φ` preserves adjacency forward. -/
  adj : ∀ {u v : V₁}, G₁.Adj u v → G₂.Adj (φ u) (φ v)
  /-- `φ` is injective on each neighborhood `G₁.neighborSet u`. -/
  injOn_neighborSet : ∀ u : V₁, Set.InjOn φ (G₁.neighborSet u)
  /-- `φ` maps `G₁.neighborSet u` onto `G₂.neighborSet (φ u)`. -/
  surjOn_neighborSet : ∀ u : V₁, Set.SurjOn φ (G₁.neighborSet u) (G₂.neighborSet (φ u))

namespace GraphCovering

variable {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {φ : V₁ → V₂}

/-- Pushing neighbor multisets forward along a `GraphCovering` yields the neighbor multiset in the
base graph. -/
theorem map_neighborFinset_val [G₁.LocallyFinite] [G₂.LocallyFinite]
    (hφ : GraphCovering G₁ G₂ φ) (u : V₁) :
    (G₁.neighborFinset u).val.map φ = (G₂.neighborFinset (φ u)).val := by
  classical
  have hinj : Set.InjOn φ (G₁.neighborFinset u : Set V₁) := by
    rw [SimpleGraph.coe_neighborFinset]
    exact hφ.injOn_neighborSet u
  have himg : (G₁.neighborFinset u).image φ = G₂.neighborFinset (φ u) := by
    ext v'
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
    exact ⟨fun ⟨w, hw, h⟩ => h ▸ hφ.adj hw, fun hv' => hφ.surjOn_neighborSet u hv'⟩
  rw [← himg, Finset.image_val_of_injOn hinj]

/-- A `GraphCovering` preserves vertex degrees. -/
theorem degree_eq [G₁.LocallyFinite] [G₂.LocallyFinite]
    (hφ : GraphCovering G₁ G₂ φ) (u : V₁) :
    G₁.degree u = G₂.degree (φ u) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    Finset.card_def, Finset.card_def, ← hφ.map_neighborFinset_val u, Multiset.card_map]

end GraphCovering

/-- A port-preserving covering map `φ : V₁ → V₂` from `(G₁, N₁)` to `(G₂, N₂)` (after
[Angluin][Angluin1980b] and [Hirvonen and Suomela][HirvonenSuomela2020], §7.1, p. 115). -/
structure PortCovering {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] (N₁ : PortNumbering G₁) (N₂ : PortNumbering G₂)
    (φ : V₁ → V₂) : Prop where
  /-- Every vertex of `G₂` lies in the image of `φ`. -/
  surjective : Function.Surjective φ
  /-- `φ` preserves adjacency forward. -/
  adj : ∀ {u v : V₁}, G₁.Adj u v → G₂.Adj (φ u) (φ v)
  /-- `φ` preserves vertex degrees. -/
  degree_eq : ∀ u : V₁, G₁.degree u = G₂.degree (φ u)
  /-- `φ` preserves local port indices on all incident edges. -/
  port_val_eq : ∀ (u : V₁) (w : G₁.neighborSet u),
    (N₂.port (φ u) ⟨φ w.1, adj w.2⟩).val = (N₁.port u w).val

namespace PortCovering

variable {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
  [G₁.LocallyFinite] [G₂.LocallyFinite] {N₁ : PortNumbering G₁} {N₂ : PortNumbering G₂}
  {φ : V₁ → V₂}

/-- Every `PortCovering` is a neighborhood-bijective `GraphCovering`. -/
theorem toGraphCovering (hφ : PortCovering N₁ N₂ φ) : GraphCovering G₁ G₂ φ where
  surjective := hφ.surjective
  adj := hφ.adj
  injOn_neighborSet u w₁ hw₁ w₂ hw₂ heq := by
    have hsub' : (⟨φ w₁, hφ.adj hw₁⟩ : G₂.neighborSet (φ u)) = ⟨φ w₂, hφ.adj hw₂⟩ :=
      Subtype.ext heq
    have hp : (N₁.port u ⟨w₁, hw₁⟩).val = (N₁.port u ⟨w₂, hw₂⟩).val := by
      rw [← hφ.port_val_eq u ⟨w₁, hw₁⟩, ← hφ.port_val_eq u ⟨w₂, hw₂⟩, hsub']
    exact congrArg Subtype.val ((N₁.port u).injective (Fin.ext hp))
  surjOn_neighborSet u v' hv' := by
    let j : Fin (G₂.degree (φ u)) := N₂.port (φ u) ⟨v', hv'⟩
    let i : Fin (G₁.degree u) := ⟨j.val, (hφ.degree_eq u).symm ▸ j.isLt⟩
    let w := (N₁.port u).symm i
    refine ⟨w.1, w.2, ?_⟩
    have hp : (N₂.port (φ u) ⟨φ w.1, hφ.adj w.2⟩).val = j.val := by
      rw [hφ.port_val_eq u w]
      simp only [w, Equiv.apply_symm_apply, i]
    exact congrArg Subtype.val ((N₂.port (φ u)).injective (Fin.ext hp))

end PortCovering

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): on synchronous
simple-graph networks, if `φ : V₁ → V₂` is a `GraphCovering` preserving local inputs, then every
node `u : V₁` has the exact same local state as `φ u` in every round `r : ℕ`. -/
theorem BroadcastProtocol.state_eq_of_graphCovering {V₁ V₂ I S M O : Type*}
    (P : BroadcastProtocol I S M O) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {φ : V₁ → V₂} (hφ : GraphCovering G₁ G₂ φ)
    {x₁ : V₁ → I} {x₂ : V₂ → I} (hx : ∀ u, x₁ u = x₂ (φ u)) (r : ℕ) (u : V₁) :
    P.state G₁ x₁ r u = P.state G₂ x₂ r (φ u) := by
  induction r generalizing u with
  | zero => simp only [state_zero, hx u]
  | succ r ih =>
    rw [state_succ, state_succ, ih u]
    congr 1
    have hcongr :
        ((G₁.neighborFinset u).val.map fun w => P.send r (P.state G₁ x₁ r w)) =
        (G₁.neighborFinset u).val.map ((fun v => P.send r (P.state G₂ x₂ r v)) ∘ φ) :=
      Multiset.map_congr rfl fun w _ => by
        dsimp only [Function.comp_apply]
        rw [ih w]
    rw [hcongr, ← Multiset.map_map, hφ.map_neighborFinset_val u]

/-- Output invariance of `BroadcastProtocol.run` along a `GraphCovering`. -/
theorem BroadcastProtocol.run_eq_of_graphCovering {V₁ V₂ I S M O : Type*}
    (P : BroadcastProtocol I S M O) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {φ : V₁ → V₂} (hφ : GraphCovering G₁ G₂ φ)
    {x₁ : V₁ → I} {x₂ : V₂ → I} (hx : ∀ u, x₁ u = x₂ (φ u)) (r : ℕ) (u : V₁) :
    P.run G₁ x₁ r u = P.run G₂ x₂ r (φ u) :=
  congrArg P.output (P.state_eq_of_graphCovering hφ hx r u)

private theorem portRecv_congr {S M : Type*} (P_recv : ℕ → (d : ℕ) → S → (Fin d → M) → S)
    {r d₁ d₂ : ℕ} (hd : d₁ = d₂) {s₁ s₂ : S} (hs : s₁ = s₂)
    {m₁ : Fin d₁ → M} {m₂ : Fin d₂ → M}
    (hm : ∀ (i₁ : Fin d₁) (i₂ : Fin d₂), i₁.val = i₂.val → m₁ i₁ = m₂ i₂) :
    P_recv r d₁ s₁ m₁ = P_recv r d₂ s₂ m₂ := by
  subst hd hs
  exact congrArg _ (funext fun i => hm i i rfl)

private theorem portSend_congr {S M : Type*} (P_send : ℕ → (d : ℕ) → S → Fin d → M)
    {r d₁ d₂ : ℕ} (hd : d₁ = d₂) {s₁ s₂ : S} (hs : s₁ = s₂)
    {j₁ : Fin d₁} {j₂ : Fin d₂} (hj : j₁.val = j₂.val) :
    P_send r d₁ s₁ j₁ = P_send r d₂ s₂ j₂ := by
  subst hd hs
  cases Fin.ext hj
  rfl

/-- Step towards `#7505` (not the cited endpoint, after Theorem 7.1 of
[Hirvonen and Suomela][HirvonenSuomela2020], pp. 118–119, and [Angluin][Angluin1980b]): on
synchronous simple-graph port-numbered networks, if `φ` is a `PortCovering` preserving local
inputs, then every deterministic `PortProtocol` produces identical states along fibers in every
round `r : ℕ`. -/
theorem PortProtocol.state_eq_of_portCovering {V₁ V₂ I S M O : Type*}
    (P : PortProtocol I S M O) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {N₁ : PortNumbering G₁} {N₂ : PortNumbering G₂}
    {φ : V₁ → V₂} (hφ : PortCovering N₁ N₂ φ)
    {x₁ : V₁ → I} {x₂ : V₂ → I} (hx : ∀ u, x₁ u = x₂ (φ u)) (r : ℕ) (u : V₁) :
    P.state N₁ x₁ r u = P.state N₂ x₂ r (φ u) := by
  induction r generalizing u with
  | zero => simp only [state_zero, hφ.degree_eq u, hx u]
  | succ r ih =>
    rw [state_succ, state_succ]
    refine portRecv_congr P.recv (hφ.degree_eq u) (ih u) fun i₁ i₂ hi => ?_
    let w₁ := (N₁.port u).symm i₁
    have hw₂ : (N₂.port (φ u)).symm i₂ = ⟨φ w₁.1, hφ.adj w₁.2⟩ := by
      apply (N₂.port (φ u)).injective
      apply Fin.ext
      rw [Equiv.apply_symm_apply, hφ.port_val_eq u w₁]
      simpa only [w₁, Equiv.apply_symm_apply] using hi.symm
    dsimp only
    rw [hw₂]
    exact portSend_congr P.send (hφ.degree_eq w₁.1) (ih w₁.1)
      (hφ.port_val_eq w₁.1 ⟨u, w₁.2.symm⟩).symm

/-- Output invariance of `PortProtocol.run` along a `PortCovering`. -/
theorem PortProtocol.run_eq_of_portCovering {V₁ V₂ I S M O : Type*}
    (P : PortProtocol I S M O) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {N₁ : PortNumbering G₁} {N₂ : PortNumbering G₂}
    {φ : V₁ → V₂} (hφ : PortCovering N₁ N₂ φ)
    {x₁ : V₁ → I} {x₂ : V₂ → I} (hx : ∀ u, x₁ u = x₂ (φ u)) (r : ℕ) (u : V₁) :
    P.run N₁ x₁ r u = P.run N₂ x₂ r (φ u) :=
  congrArg P.output (P.state_eq_of_portCovering hφ hx r u)

/-! ### Symmetry-breaking impossibility corollaries -/

/-- A Boolean node labeling `f : V → Bool` elects a unique leader when exactly one vertex outputs
`true`. -/
@[expose] def ElectsUniqueLeader {V : Type*} (f : V → Bool) : Prop :=
  ∃! u : V, f u = true

/-- On a finite vertex set, `ElectsUniqueLeader f` holds iff the filter of `true` vertices has
cardinality `1`. -/
theorem electsUniqueLeader_iff_card_eq_one {V : Type*} [Fintype V] (f : V → Bool) :
    ElectsUniqueLeader f ↔ (Finset.univ.filter fun u => f u = true).card = 1 := by
  rw [ElectsUniqueLeader, Finset.card_eq_one]
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨u, Finset.ext fun v => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hv => huniq v hv, fun hv => hv ▸ hu⟩
  · rintro ⟨u, hu⟩
    have hmem : ∀ v, f v = true ↔ v = u := fun v => by
      have hv := Finset.ext_iff.1 hu v
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using hv
    exact ⟨u, (hmem u).2 rfl, fun v hv => (hmem v).1 hv⟩

/-- If `f : V₁ → Bool` factors through `φ : V₁ → V₂` and every image `φ u` has a second distinct
preimage, then `f` cannot elect a unique leader. -/
theorem not_electsUniqueLeader_of_factorsThrough {V₁ V₂ : Type*} {φ : V₁ → V₂} {f : V₁ → Bool}
    {g : V₂ → Bool} (hfg : ∀ u, f u = g (φ u))
    (hfiber : ∀ y : V₂, ∃ u₁ u₂ : V₁, u₁ ≠ u₂ ∧ φ u₁ = y ∧ φ u₂ = y) :
    ¬ ElectsUniqueLeader f := by
  rintro ⟨u, hu, huniq⟩
  obtain ⟨u₁, u₂, hne, h1, h2⟩ := hfiber (φ u)
  have hg : g (φ u) = true := (hfg u).symm.trans hu
  have hu₁ : u₁ = u := huniq u₁ ((hfg u₁).trans (h1.symm ▸ hg))
  have hu₂ : u₂ = u := huniq u₂ ((hfg u₂).trans (h2.symm ▸ hg))
  exact hne (hu₁.trans hu₂.symm)

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): if `(G₁, N₁)`
covers `(G₂, N₂)` via `φ` with at least two vertices in every fiber, no deterministic
`PortProtocol` with uniform initial input `x₀` elects a unique leader in any round `r`. -/
theorem PortProtocol.not_electsUniqueLeader_of_portCovering {V₁ V₂ I S M : Type*}
    (P : PortProtocol I S M Bool) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {N₁ : PortNumbering G₁} {N₂ : PortNumbering G₂}
    {φ : V₁ → V₂} (hφ : PortCovering N₁ N₂ φ)
    (hfiber : ∀ y : V₂, ∃ u₁ u₂ : V₁, u₁ ≠ u₂ ∧ φ u₁ = y ∧ φ u₂ = y)
    (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run N₁ (fun _ => x₀) r) :=
  not_electsUniqueLeader_of_factorsThrough
    (P.run_eq_of_portCovering hφ (x₂ := fun _ => x₀) (fun _ => rfl) r) hfiber

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): if `G₁` covers
`G₂` via `φ` with at least two vertices in every fiber, no deterministic `BroadcastProtocol` with
uniform initial input `x₀` elects a unique leader in any round `r`. -/
theorem BroadcastProtocol.not_electsUniqueLeader_of_graphCovering {V₁ V₂ I S M : Type*}
    (P : BroadcastProtocol I S M Bool) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {φ : V₁ → V₂} (hφ : GraphCovering G₁ G₂ φ)
    (hfiber : ∀ y : V₂, ∃ u₁ u₂ : V₁, u₁ ≠ u₂ ∧ φ u₁ = y ∧ φ u₂ = y)
    (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run G₁ (fun _ => x₀) r) :=
  not_electsUniqueLeader_of_factorsThrough
    (P.run_eq_of_graphCovering hφ (x₂ := fun _ => x₀) (fun _ => rfl) r) hfiber

/-- If a coloring `c₁ : V₁ → Fin q` of `G₁` factors as `c₂ ∘ φ` along a `GraphCovering` `φ` onto
`G₂`, and `c₁` is proper on `G₁`, then `G₂` is `q`-colorable. -/
theorem GraphCovering.colorable_of_isProperColoring {V₁ V₂ : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {φ : V₁ → V₂} (hφ : GraphCovering G₁ G₂ φ)
    {q : ℕ} {c₁ : V₁ → Fin q} {c₂ : V₂ → Fin q}
    (hc : ∀ u, c₁ u = c₂ (φ u)) (hprop : G₁.IsProperColoring c₁) :
    G₂.Colorable q := by
  refine ⟨SimpleGraph.Coloring.mk c₂ fun {y₁ y₂} hy => ?_⟩
  obtain ⟨u₁, rfl⟩ := hφ.surjective y₁
  obtain ⟨u₂, hu₂, rfl⟩ := hφ.surjOn_neighborSet u₁ hy
  rw [← hc u₁, ← hc u₂]
  exact (SimpleGraph.isProperColoring_iff G₁).1 hprop u₁ u₂ hu₂

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): if `(G₁, N₁)`
covers `(G₂, N₂)` and `¬ G₂.Colorable q`, then no deterministic `PortProtocol` with uniform initial
input `x₀` outputs a proper `Fin q`-coloring of `G₁` in any round `r`, even if `G₁` itself is
`q`-colorable. -/
theorem PortProtocol.not_isProperColoring_of_portCovering {V₁ V₂ I S M : Type*}
    {q : ℕ} (P : PortProtocol I S M (Fin q)) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {N₁ : PortNumbering G₁} {N₂ : PortNumbering G₂}
    {φ : V₁ → V₂} (hφ : PortCovering N₁ N₂ φ) (hnot : ¬ G₂.Colorable q)
    (x₀ : I) (r : ℕ) :
    ¬ G₁.IsProperColoring (P.run N₁ (fun _ => x₀) r) := fun hprop =>
  hnot (hφ.toGraphCovering.colorable_of_isProperColoring
    (P.run_eq_of_portCovering hφ (x₂ := fun _ => x₀) (fun _ => rfl) r) hprop)

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): if `G₁` covers
`G₂` and `¬ G₂.Colorable q`, then no deterministic `BroadcastProtocol` with uniform initial input
`x₀` outputs a proper `Fin q`-coloring of `G₁` in any round `r`. -/
theorem BroadcastProtocol.not_isProperColoring_of_graphCovering {V₁ V₂ I S M : Type*}
    {q : ℕ} (P : BroadcastProtocol I S M (Fin q)) {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    [G₁.LocallyFinite] [G₂.LocallyFinite] {φ : V₁ → V₂} (hφ : GraphCovering G₁ G₂ φ)
    (hnot : ¬ G₂.Colorable q) (x₀ : I) (r : ℕ) :
    ¬ G₁.IsProperColoring (P.run G₁ (fun _ => x₀) r) := fun hprop =>
  hnot (hφ.colorable_of_isProperColoring
    (P.run_eq_of_graphCovering hφ (x₂ := fun _ => x₀) (fun _ => rfl) r) hprop)

/-! ### Bipartite double cover `G × K₂` -/

/-- The bipartite (Kronecker) double cover of `G : SimpleGraph V` on `Bool × V`: `(b₁, u)` and
`(b₂, v)` are adjacent iff `b₁ ≠ b₂` and `G.Adj u v`. -/
@[expose] def bipartiteDoubleCover {V : Type*} (G : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj p q := p.1 ≠ q.1 ∧ G.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (bipartiteDoubleCover G).Adj :=
  fun p q => inferInstanceAs (Decidable (p.1 ≠ q.1 ∧ G.Adj p.2 q.2))

/-- Every bipartite double cover `bipartiteDoubleCover G` is 2-colorable, regardless of the
chromatic number of `G`. -/
theorem bipartiteDoubleCover_colorable_two {V : Type*} (G : SimpleGraph V) :
    (bipartiteDoubleCover G).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun p => if p.1 then (1 : Fin 2) else (0 : Fin 2)) fun {p q} hpq => by
    rcases p with ⟨b₁, _⟩
    rcases q with ⟨b₂, _⟩
    cases b₁ <;> cases b₂ <;> first | exact absurd rfl hpq.1 | simp⟩

/-- `Prod.snd : Bool × V → V` is a 2-fold `GraphCovering` from `bipartiteDoubleCover G` onto `G`. -/
theorem graphCovering_bipartiteDoubleCover {V : Type*} (G : SimpleGraph V) :
    GraphCovering (bipartiteDoubleCover G) G Prod.snd where
  surjective v := ⟨(false, v), rfl⟩
  adj h := h.2
  injOn_neighborSet := by
    rintro ⟨b, u⟩ ⟨b₁, w₁⟩ hw₁ ⟨b₂, w₂⟩ hw₂ (heq : w₁ = w₂)
    subst heq
    have hb₁ : b₁ = !b := by cases b <;> cases b₁ <;> first | exact absurd rfl hw₁.1 | rfl
    have hb₂ : b₂ = !b := by cases b <;> cases b₂ <;> first | exact absurd rfl hw₂.1 | rfl
    rw [hb₁, hb₂]
  surjOn_neighborSet := by
    rintro ⟨b, u⟩ v hv
    exact ⟨(!b, v), ⟨Bool.not_ne_self b |>.symm, hv⟩, rfl⟩

/-- Lift any `PortNumbering G` to `bipartiteDoubleCover G` so that `Prod.snd` is a `PortCovering`.
-/
def PortNumbering.bipartiteDoubleCover {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (N : PortNumbering G) :
    PortNumbering (LocalGraph.bipartiteDoubleCover G) where
  port := fun ⟨b, u⟩ =>
    let hdeg : (LocalGraph.bipartiteDoubleCover G).degree (b, u) = G.degree u :=
      (graphCovering_bipartiteDoubleCover G).degree_eq (b, u)
    { toFun := fun ⟨⟨_, v⟩, _, hadj⟩ =>
        ⟨(N.port u ⟨v, hadj⟩).val, hdeg.symm ▸ (N.port u ⟨v, hadj⟩).isLt⟩
      invFun := fun i =>
        let w := (N.port u).symm ⟨i.val, hdeg ▸ i.isLt⟩
        ⟨(!b, w.1), ⟨(Bool.not_ne_self b).symm, w.2⟩⟩
      left_inv := fun ⟨⟨b', w'⟩, hne, hadj⟩ => by
        apply Subtype.ext
        apply Prod.ext
        · dsimp only
          cases b <;> cases b' <;> first | exact absurd rfl hne | rfl
        · dsimp only
          exact congrArg Subtype.val ((N.port u).symm_apply_apply ⟨w', hadj⟩)
      right_inv := fun i => by
        apply Fin.ext
        dsimp only
        exact congrArg Fin.val ((N.port u).apply_symm_apply ⟨i.val, hdeg ▸ i.isLt⟩) }

/-- `Prod.snd` is a `PortCovering` from `N.bipartiteDoubleCover` onto `N`. -/
theorem portCovering_bipartiteDoubleCover {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (N : PortNumbering G) :
    PortCovering N.bipartiteDoubleCover N Prod.snd where
  surjective v := ⟨(false, v), rfl⟩
  adj h := h.2
  degree_eq p := (graphCovering_bipartiteDoubleCover G).degree_eq p
  port_val_eq := fun ⟨_, _⟩ ⟨⟨_, _⟩, _, _⟩ => rfl

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): no deterministic
anonymous `PortProtocol` elects a unique leader on `bipartiteDoubleCover G` under
`N.bipartiteDoubleCover` in any round `r`. -/
theorem PortProtocol.not_electsUniqueLeader_bipartiteDoubleCover {V I S M : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (N : PortNumbering G)
    (P : PortProtocol I S M Bool) (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run N.bipartiteDoubleCover (fun _ => x₀) r) :=
  P.not_electsUniqueLeader_of_portCovering (portCovering_bipartiteDoubleCover N)
    (fun v => ⟨(false, v), (true, v), fun h => Bool.false_ne_true (Prod.mk.inj h).1, rfl, rfl⟩)
    x₀ r

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): whenever
`¬ G.Colorable q`, no deterministic anonymous `PortProtocol` computes a proper `Fin q`-coloring of
`bipartiteDoubleCover G` under `N.bipartiteDoubleCover` in any round `r` (even for `q = 2`, where
`bipartiteDoubleCover G` is always 2-colorable). -/
theorem PortProtocol.not_isProperColoring_bipartiteDoubleCover {V I S M : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (N : PortNumbering G) {q : ℕ}
    (hq : ¬ G.Colorable q) (P : PortProtocol I S M (Fin q)) (x₀ : I) (r : ℕ) :
    ¬ (bipartiteDoubleCover G).IsProperColoring (P.run N.bipartiteDoubleCover (fun _ => x₀) r) :=
  P.not_isProperColoring_of_portCovering (portCovering_bipartiteDoubleCover N) hq x₀ r

/-! ### Explicit `C₆ → C₃` cycle double cover -/

/-- The 2-fold covering projection `i ↦ i mod 3` from `C₆` (`Fin 6`) onto `C₃` (`Fin 3`). -/
@[expose] def cycleDoubleCoverMap (i : Fin 6) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

/-- `C₆` (`SimpleGraph.cycleGraph 6`) is 2-colorable (`χ(C₆) = 2`). -/
theorem cycleGraph_six_colorable_two : (SimpleGraph.cycleGraph 6).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun i : Fin 6 => ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)
    fun {u v} huv => by
      revert u v huv
      decide⟩

/-- `C₃` (`SimpleGraph.cycleGraph 3`) is not 2-colorable (`χ(C₃) = 3`). -/
theorem not_cycleGraph_three_colorable_two : ¬ (SimpleGraph.cycleGraph 3).Colorable 2 := by
  rintro ⟨C⟩
  have h01 : C 0 ≠ C 1 := C.valid (by decide)
  have h12 : C 1 ≠ C 2 := C.valid (by decide)
  have h02 : C 0 ≠ C 2 := C.valid (by decide)
  have hc0 := (C 0).isLt
  have hc1 := (C 1).isLt
  have hc2 := (C 2).isLt
  omega

/-- `cycleDoubleCoverMap` is a 2-fold `GraphCovering` from `C₆` onto `C₃`. -/
theorem graphCovering_cycleGraph_six_three :
    GraphCovering (SimpleGraph.cycleGraph 6) (SimpleGraph.cycleGraph 3) cycleDoubleCoverMap where
  surjective y := ⟨⟨y.val, by omega⟩, Fin.ext (Nat.mod_eq_of_lt y.isLt)⟩
  adj := by
    intro u v huv
    revert u v huv
    decide
  injOn_neighborSet := by
    intro u w₁ hw₁ w₂ hw₂ heq
    revert u w₁ w₂ hw₁ hw₂ heq
    decide
  surjOn_neighborSet := by
    intro u v' hv'
    change ∃ w : Fin 6, (SimpleGraph.cycleGraph 6).Adj u w ∧ cycleDoubleCoverMap w = v'
    revert u v' hv'
    decide

/-- Oriented port numbering on `SimpleGraph.cycleGraph (m + 3)`: port `0` points to successor
`u + 1` and port `1` points to predecessor `u - 1`. -/
@[expose] def cycleGraphPortNumbering (m : ℕ) :
    PortNumbering (SimpleGraph.cycleGraph (m + 3)) where
  port u :=
    let hdeg : (SimpleGraph.cycleGraph (m + 3)).degree u = 2 :=
      SimpleGraph.cycleGraph_degree_three_le
    have hadj_add : u + 1 ∈ (SimpleGraph.cycleGraph (m + 3)).neighborSet u :=
      SimpleGraph.cycleGraph_adj.2 (Or.inr (add_sub_cancel_left u 1))
    have hadj_sub : u - 1 ∈ (SimpleGraph.cycleGraph (m + 3)).neighborSet u :=
      SimpleGraph.cycleGraph_adj.2 (Or.inl (sub_sub_cancel u 1))
    { toFun := fun w => if w.1 = u + 1 then ⟨0, by omega⟩ else ⟨1, by omega⟩
      invFun := fun i => if i.val = 0 then ⟨u + 1, hadj_add⟩ else ⟨u - 1, hadj_sub⟩
      left_inv := fun ⟨w, hw⟩ => by
        apply Subtype.ext
        dsimp only
        have hmem : w ∈ ({u - 1, u + 1} : Set (Fin (m + 3))) :=
          SimpleGraph.cycleGraph_neighborSet ▸ hw
        have hne : u - 1 ≠ u + 1 := by
          simp only [ne_eq, sub_eq_iff_eq_add, add_assoc u, left_eq_add]
          exact ne_of_beq_false rfl
        rcases Set.mem_insert_iff.1 hmem with rfl | hadd
        · simp only [hne, Nat.one_ne_zero, ↓reduceIte]
        · rcases Set.mem_singleton_iff.1 hadd with rfl
          simp only [↓reduceIte]
      right_inv := fun i => by
        apply Fin.ext
        have hi : i.val < 2 := hdeg ▸ i.isLt
        have hne : u - 1 ≠ u + 1 := by
          simp only [ne_eq, sub_eq_iff_eq_add, add_assoc u, left_eq_add]
          exact ne_of_beq_false rfl
        dsimp only
        obtain h0 | h1 : i.val = 0 ∨ i.val = 1 := by omega
        · simp only [h0, ↓reduceIte]
        · simp only [h1, Nat.one_ne_zero, ↓reduceIte, hne] }

/-- `cycleDoubleCoverMap` is a `PortCovering` from `(C₆, cycleGraphPortNumbering 3)` onto
`(C₃, cycleGraphPortNumbering 0)`. -/
theorem portCovering_cycleGraph_six_three :
    PortCovering (cycleGraphPortNumbering 3) (cycleGraphPortNumbering 0) cycleDoubleCoverMap where
  surjective := graphCovering_cycleGraph_six_three.surjective
  adj h := graphCovering_cycleGraph_six_three.adj h
  degree_eq _ := by
    rw [SimpleGraph.cycleGraph_degree_three_le, SimpleGraph.cycleGraph_degree_three_le]
  port_val_eq := by
    rintro u ⟨w, hw⟩
    dsimp only [cycleGraphPortNumbering]
    revert u w hw
    decide

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): no deterministic
anonymous `BroadcastProtocol` elects a unique leader on `SimpleGraph.cycleGraph 6` in any round `r`.
-/
theorem BroadcastProtocol.not_electsUniqueLeader_cycleGraph_six {I S M : Type*}
    (P : BroadcastProtocol I S M Bool) (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run (SimpleGraph.cycleGraph 6) (fun _ => x₀) r) :=
  P.not_electsUniqueLeader_of_graphCovering graphCovering_cycleGraph_six_three
    (fun y => ⟨⟨y.val, by omega⟩, ⟨y.val + 3, by omega⟩,
      fun h => by have := congrArg Fin.val h; dsimp at this; omega,
      Fin.ext (Nat.mod_eq_of_lt y.isLt),
      Fin.ext (by dsimp [cycleDoubleCoverMap]; omega)⟩)
    x₀ r

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b]): although `C₆` is
2-colorable (`cycleGraph_six_colorable_two`), no deterministic anonymous `BroadcastProtocol`
outputs a proper 2-coloring of `SimpleGraph.cycleGraph 6` in any round `r`. -/
theorem BroadcastProtocol.not_twoColoring_cycleGraph_six {I S M : Type*}
    (P : BroadcastProtocol I S M (Fin 2)) (x₀ : I) (r : ℕ) :
    ¬ (SimpleGraph.cycleGraph 6).IsProperColoring
      (P.run (SimpleGraph.cycleGraph 6) (fun _ => x₀) r) :=
  P.not_isProperColoring_of_graphCovering graphCovering_cycleGraph_six_three
    not_cycleGraph_three_colorable_two x₀ r

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b] and
[Hirvonen and Suomela][HirvonenSuomela2020], §7.1–7.3): no deterministic `PortProtocol` with uniform
initial input `x₀` elects a unique leader on `SimpleGraph.cycleGraph 6` under
`cycleGraphPortNumbering 3` in any round `r`. -/
theorem PortProtocol.not_electsUniqueLeader_cycleGraphPortNumbering_six {I S M : Type*}
    (P : PortProtocol I S M Bool) (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run (cycleGraphPortNumbering 3) (fun _ => x₀) r) :=
  P.not_electsUniqueLeader_of_portCovering portCovering_cycleGraph_six_three
    (fun y => ⟨⟨y.val, by omega⟩, ⟨y.val + 3, by omega⟩,
      fun h => by have := congrArg Fin.val h; dsimp at this; omega,
      Fin.ext (Nat.mod_eq_of_lt y.isLt),
      Fin.ext (by dsimp [cycleDoubleCoverMap]; omega)⟩)
    x₀ r

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b] and
[Hirvonen and Suomela][HirvonenSuomela2020], §7.2–7.3): although `C₆` is 2-colorable
(`cycleGraph_six_colorable_two`), no deterministic `PortProtocol` with uniform initial input `x₀`
outputs a proper 2-coloring of `SimpleGraph.cycleGraph 6` under `cycleGraphPortNumbering 3` in any
round `r`, because `(C₆, cycleGraphPortNumbering 3)` double-covers `(C₃, cycleGraphPortNumbering 0)`
(`χ(C₃) = 3`). -/
theorem PortProtocol.not_twoColoring_cycleGraphPortNumbering_six {I S M : Type*}
    (P : PortProtocol I S M (Fin 2)) (x₀ : I) (r : ℕ) :
    ¬ (SimpleGraph.cycleGraph 6).IsProperColoring
      (P.run (cycleGraphPortNumbering 3) (fun _ => x₀) r) :=
  P.not_isProperColoring_of_portCovering portCovering_cycleGraph_six_three
    not_cycleGraph_three_colorable_two x₀ r

/-! ### Symmetric `K₃,₃` (`completeBipartiteGraph (Fin 3) (Fin 3)`) client -/

/-- Decidability of adjacency in `completeBipartiteGraph V W`. -/
scoped instance instDecidableRelCompleteBipartiteGraphAdj {V W : Type*} :
    DecidableRel (completeBipartiteGraph V W).Adj :=
  fun v w => inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

/-- Every vertex of `K₃,₃` (`completeBipartiteGraph (Fin 3) (Fin 3)`) has degree `3`. -/
theorem degree_k33 (u : Fin 3 ⊕ Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).degree u = 3 := by
  revert u
  decide

/-- Symmetric port numbering on `K₃,₃` (`completeBipartiteGraph (Fin 3) (Fin 3)`): left vertex
`inl i` connects via port `k` to `inr (i + k)`, and right vertex `inr j` connects via port `k` to
`inl (j - k)`. -/
@[expose] def k33PortNumbering :
    PortNumbering (completeBipartiteGraph (Fin 3) (Fin 3)) where
  port u :=
    have hdeg := degree_k33 u
    have hlt3 : ∀ x : Fin 3, x.val < (completeBipartiteGraph (Fin 3) (Fin 3)).degree u :=
      fun x => by have := x.isLt; omega
    { toFun := fun w =>
        match u, w with
        | Sum.inl i, ⟨Sum.inr j, _⟩ => ⟨(j - i).val, hlt3 (j - i)⟩
        | Sum.inr j, ⟨Sum.inl i, _⟩ => ⟨(j - i).val, hlt3 (j - i)⟩
        | Sum.inl _, ⟨Sum.inl _, hw⟩ => False.elim (by simp at hw)
        | Sum.inr _, ⟨Sum.inr _, hw⟩ => False.elim (by simp at hw)
      invFun := fun p =>
        let k : Fin 3 := ⟨p.val, by have := p.isLt; omega⟩
        match u with
        | Sum.inl i => ⟨Sum.inr (i + k), by simp⟩
        | Sum.inr j => ⟨Sum.inl (j - k), by simp⟩
      left_inv := fun ⟨w, hw⟩ => by
        apply Subtype.ext
        rcases u with i | j <;> rcases w with i' | j'
        · exact False.elim (by simp at hw)
        · dsimp only
          congr 1
          exact add_sub_cancel i j'
        · dsimp only
          congr 1
          exact sub_sub_self j i'
        · exact False.elim (by simp at hw)
      right_inv := fun p => by
        apply Fin.ext
        rcases u with i | j
        · dsimp only
          exact congrArg Fin.val (add_sub_cancel_left i (⟨p.val, by have := p.isLt; omega⟩ : Fin 3))
        · dsimp only
          exact congrArg Fin.val (sub_sub_self j (⟨p.val, by have := p.isLt; omega⟩ : Fin 3)) }

/-- For every target vertex `v` of `K₃,₃`, there is a port-preserving self-covering of
`k33PortNumbering` taking `Sum.inl 0` to `v`. -/
private theorem exists_portCovering_k33 (v : Fin 3 ⊕ Fin 3) :
    ∃ φ : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3,
      PortCovering k33PortNumbering k33PortNumbering φ ∧ φ (Sum.inl 0) = v := by
  have hsub_fin3 : ∀ c x y : Fin 3, (c - x) - (c - y) = y - x := by decide
  rcases v with c | c
  · refine ⟨fun x => match x with | Sum.inl i => Sum.inl (i + c) | Sum.inr j => Sum.inr (j + c),
      ?_, by simp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | j)
      · exact ⟨Sum.inl (i - c), by simp⟩
      · exact ⟨Sum.inr (j - c), by simp⟩
    · intro x y hxy
      rcases x with i | j <;> rcases y with i' | j' <;> simp_all
    · intro x
      rw [degree_k33, degree_k33]
    · rintro (i | j) ⟨(i' | j'), hw⟩
      · exact False.elim (by simp at hw)
      · dsimp only [k33PortNumbering]
        exact congrArg Fin.val (add_sub_add_right_eq_sub j' i c)
      · dsimp only [k33PortNumbering]
        exact congrArg Fin.val (add_sub_add_right_eq_sub j i' c)
      · exact False.elim (by simp at hw)
  · refine ⟨fun x => match x with | Sum.inl i => Sum.inr (c - i) | Sum.inr j => Sum.inl (c - j),
      ?_, by simp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | j)
      · exact ⟨Sum.inr (c - i), by simp⟩
      · exact ⟨Sum.inl (c - j), by simp⟩
    · intro x y hxy
      rcases x with i | j <;> rcases y with i' | j' <;> simp_all
    · intro x
      rw [degree_k33, degree_k33]
    · rintro (i | j) ⟨(i' | j'), hw⟩
      · exact False.elim (by simp at hw)
      · dsimp only [k33PortNumbering]
        exact congrArg Fin.val (hsub_fin3 c i j')
      · dsimp only [k33PortNumbering]
        exact congrArg Fin.val (hsub_fin3 c i' j)
      · exact False.elim (by simp at hw)

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b] and
[Hirvonen and Suomela][HirvonenSuomela2020], §7.1–7.2): under `k33PortNumbering` and uniform initial
input `x₀`, all six vertices of `K₃,₃` share the exact same local state in every round `r : ℕ`. -/
theorem PortProtocol.state_k33PortNumbering_eq {I S M O : Type*} (P : PortProtocol I S M O) (x₀ : I)
    (r : ℕ) (u v : Fin 3 ⊕ Fin 3) :
    P.state k33PortNumbering (fun _ => x₀) r u =
      P.state k33PortNumbering (fun _ => x₀) r v := by
  suffices h0 : ∀ w, P.state k33PortNumbering (fun _ => x₀) r (Sum.inl 0) =
      P.state k33PortNumbering (fun _ => x₀) r w from (h0 u).symm.trans (h0 v)
  intro w
  obtain ⟨φ, hφ, hφ0⟩ := exists_portCovering_k33 w
  rw [← hφ0]
  exact P.state_eq_of_portCovering hφ (x₂ := fun _ => x₀) (fun _ => rfl) r (Sum.inl 0)

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b] and
[Hirvonen and Suomela][HirvonenSuomela2020], §7.1–7.2): no deterministic anonymous `PortProtocol`
elects a unique leader on `K₃,₃` under `k33PortNumbering` in any round `r`. -/
theorem PortProtocol.not_electsUniqueLeader_k33PortNumbering {I S M : Type*}
    (P : PortProtocol I S M Bool) (x₀ : I) (r : ℕ) :
    ¬ ElectsUniqueLeader (P.run k33PortNumbering (fun _ => x₀) r) := by
  rintro ⟨u, hu, huniq⟩
  have hstate := P.state_k33PortNumbering_eq x₀ r (Sum.inl 0) (Sum.inr 0)
  have hrun : P.run k33PortNumbering (fun _ => x₀) r (Sum.inl 0) =
      P.run k33PortNumbering (fun _ => x₀) r (Sum.inr 0) :=
    congrArg P.output hstate
  have h0u := P.state_k33PortNumbering_eq x₀ r (Sum.inl 0) u
  have hl0 : P.run k33PortNumbering (fun _ => x₀) r (Sum.inl 0) = true :=
    (congrArg P.output h0u).trans hu
  have hl1 : P.run k33PortNumbering (fun _ => x₀) r (Sum.inr 0) = true := hrun.symm.trans hl0
  exact Sum.inl_ne_inr ((huniq (Sum.inl 0) hl0).trans (huniq (Sum.inr 0) hl1).symm)

/-- Step towards `#7505` (not the cited endpoint, after [Angluin][Angluin1980b] and
[Hirvonen and Suomela][HirvonenSuomela2020], §7.1–7.2): although `K₃,₃` is bipartite
(2-colorable), no deterministic anonymous `PortProtocol` computes a proper `Fin q`-coloring of
`K₃,₃` under `k33PortNumbering` for any `q : ℕ` in any round `r`. -/
theorem PortProtocol.not_isProperColoring_k33PortNumbering {I S M : Type*} {q : ℕ}
    (P : PortProtocol I S M (Fin q)) (x₀ : I) (r : ℕ) :
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsProperColoring
      (P.run k33PortNumbering (fun _ => x₀) r) := by
  intro hprop
  have hadj : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl 0) (Sum.inr 0) := by simp
  exact (SimpleGraph.isProperColoring_iff _).1 hprop (Sum.inl 0) (Sum.inr 0) hadj
    (congrArg P.output (P.state_k33PortNumbering_eq x₀ r (Sum.inl 0) (Sum.inr 0)))

end Cslib.Distributed.LocalGraph
