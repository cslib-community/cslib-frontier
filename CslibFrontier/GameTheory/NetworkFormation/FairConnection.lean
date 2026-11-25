/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Connectivity
public import CslibFrontier.GameTheory.Congestion.CostSharing
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CslibFrontier.Foundations.NumberTheory.Harmonic
import CslibFrontier.GameTheory.Strategic.Stability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fair connection games on directed and undirected networks

In the **fair connection game** (global connection game or Shapley network design game) of
Anshelevich, Dasgupta, Kleinberg, Tardos, Wexler and Roughgarden [AnshelevichDKTWR2008]
([TardosWexler2007], Section 19.3.1), `k` players build a subnetwork of an edge-weighted graph:

* Every edge `e` has a fixed nonnegative construction cost `edgeCost e`.
* Each player `i : ι` wants to connect its source terminal `source i` to its sink terminal
  `sink i` by choosing a simple `source i`–`sink i` path.
* Under the **Shapley equal cost-sharing rule**, the cost `edgeCost e` of each used edge is split
  equally among the `edgeLoad s e` players whose chosen paths traverse `e`, so player `i` pays
  `∑ e ∈ pathEdges, edgeCost e / edgeLoad s e` and the social cost of a profile `s` is the total
  cost `∑ e ∈ formedEdges s, edgeCost e` of the formed subnetwork.

Viewing the edges of each simple path as its resource set embeds both the directed multigraph game
(`Cslib.GameTheory.FairConnectionGame`, allowing parallel arcs and zero-cost feeder arcs) and the
undirected simple-graph game (`Cslib.GameTheory.UndirectedFairConnectionGame`, where players
traversing an undirected edge in opposite directions share its cost) into
`Cslib.GameTheory.CongestionGame.fairCostSharing` ([TardosWexler2007], Section 19.3.2). Through
that bridge:

* Rosenthal's potential `Φ s = ∑ e, edgeCost e * harmonic (edgeLoad s e)` is an **exact potential**
  ([TardosWexler2007], Lemma 19.7), sandwiched by `socialCost s ≤ Φ s ≤ H k * socialCost s`
  ([TardosWexler2007], Lemma 19.8).
* Every finite fair connection game whose terminal pairs are connected has the **finite improvement
  property** and at least one **pure Nash equilibrium** ([TardosWexler2007], Section 19.3.1).
* **Anshelevich et al.'s `H_k` theorem** ([AnshelevichDKTWR2008]; [TardosWexler2007],
  Theorem 19.10): some pure Nash equilibrium (reachable by better-response dynamics from an optimal
  network) has social cost at most `H k` times that of any strategy profile—and, equivalently, at
  most `H k` times the cost `∑ e ∈ F, edgeCost e` of any centralized Steiner subnetwork `F`
  connecting every player's terminals.
* Every fair connection game with nonnegative edge costs is **`(k, 0)`-smooth**, so **every** pure
  Nash equilibrium (and coarse correlated equilibrium) has cost at most `k` times that of any
  profile or Steiner subnetwork ([Roughgarden2015], Definition 2.1 and Theorem 3.2;
  [TardosWexler2007], Section 19.3).

Matching tightness and separation witnesses (`PoS → H_k` on directed single-sink networks vs.
`PoS = 1` on the undirected counterpart, `PoA = k` on parallel links, and a game whose socially
best pure Nash equilibrium does not minimize Rosenthal's potential) are in
`CslibFrontier/GameTheory/NetworkFormation/Witnesses.lean`.

## Main definitions

* `Cslib.GameTheory.FairConnectionGame`: fair connection game on a directed multigraph
  `src tgt : E → V` with edge costs `edgeCost` and player terminals `(source i, sink i)`.
* `Cslib.GameTheory.FairConnectionGame.Path`, `FairConnectionGame.formedEdges`,
  `FairConnectionGame.toCongestionGame`, `FairConnectionGame.toCostGame`,
  `FairConnectionGame.potential`: simple `source i`–`sink i` arc paths, formed network, congestion
  and strategic game projections, and Rosenthal's harmonic potential.
* `Cslib.GameTheory.FairConnectionGame.TerminalsConnected`,
  `FairConnectionGame.IsSteinerSubgraph`: terminal reachability and centralized Steiner arc sets.
* `Cslib.GameTheory.UndirectedFairConnectionGame`: fair connection game on an undirected
  `SimpleGraph V` with symmetric `Sym2 V` edge sharing across traversal directions.

## Main results

* `Cslib.GameTheory.FairConnectionGame.socialCost_eq_sum_formedEdges`: social cost equals the total
  cost of the formed subnetwork `⋃ i, pathEdges (s i)`.
* `Cslib.GameTheory.FairConnectionGame.potential_eq`,
  `Cslib.GameTheory.FairConnectionGame.isExactPotential_potential` ([TardosWexler2007],
  Lemma 19.7): `Φ s = ∑ e, edgeCost e * H (edgeLoad s e)` is an exact potential.
* `Cslib.GameTheory.FairConnectionGame.socialCost_le_potential`,
  `Cslib.GameTheory.FairConnectionGame.potential_le_harmonic_mul_socialCost` ([TardosWexler2007],
  Lemma 19.8): `socialCost s ≤ Φ s ≤ H k * socialCost s`.
* `Cslib.GameTheory.FairConnectionGame.hasFIP`,
  `Cslib.GameTheory.FairConnectionGame.exists_isPureNash` ([TardosWexler2007], Section 19.3.1):
  finite improvement property and pure Nash equilibrium existence.
* `Cslib.GameTheory.FairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul`,
  `Cslib.GameTheory.FairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul_steinerCost`,
  `Cslib.GameTheory.FairConnectionGame.exists_reflTransGen_isPureNash_socialCost_le_harmonic_mul`
  ([AnshelevichDKTWR2008]; [TardosWexler2007], Theorem 19.10): **price of stability at most `H_k`**
  against all strategy profiles and all centralized Steiner subnetworks.
* `Cslib.GameTheory.FairConnectionGame.isSmooth`,
  `Cslib.GameTheory.FairConnectionGame.socialCost_le_card_mul_of_isPureNash`,
  `Cslib.GameTheory.FairConnectionGame.socialCost_le_card_mul_steinerCost_of_isPureNash`
  ([Roughgarden2015], Definition 2.1; [TardosWexler2007], Section 19.3): **`(k, 0)`-smoothness and
  price of anarchy at most `k`**.
* `Cslib.GameTheory.UndirectedFairConnectionGame.isExactPotential_potential`,
  `Cslib.GameTheory.UndirectedFairConnectionGame.exists_isPureNash`,
  `Cslib.GameTheory.UndirectedFairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul`,
  `Cslib.GameTheory.UndirectedFairConnectionGame.socialCost_le_card_mul_of_isPureNash`: the
  corresponding undirected simple-graph theorems.

## References

* [AnshelevichDKTWR2008]
* [Rosenthal1973]
* [Roughgarden2015]
* [RoughgardenTardos2007]
* [TardosWexler2007]
-/

public section

/-! ### Directed Fair Connection Games -/

namespace Cslib.GameTheory

/-- A **fair connection game** (global connection game or Shapley network design game,
[AnshelevichDKTWR2008]; [TardosWexler2007], Section 19.3.1) on a directed multigraph with vertices
`V` and edges `E`: edge `e` goes from `src e` to `tgt e` with fixed construction cost `edgeCost e`,
and each player `i : ι` connects `source i` to `sink i` along a simple directed path, sharing the
cost of each used edge equally among its users. -/
structure FairConnectionGame (ι V E : Type*) where
  /-- Source endpoint of each directed edge. -/
  src : E → V
  /-- Target endpoint of each directed edge. -/
  tgt : E → V
  /-- Fixed construction cost `c_e` of edge `e`. -/
  edgeCost : E → ℝ
  /-- Source terminal `s_i` of player `i`. -/
  source : ι → V
  /-- Sink terminal `t_i` of player `i`. -/
  sink : ι → V

namespace FairConnectionGame

variable {ι V E : Type*}

section Basic

variable (G : FairConnectionGame ι V E)

/-- A strategy of player `i` in `G`: a simple directed path of arcs from `G.source i` to
`G.sink i`. -/
abbrev Path (i : ι) : Type _ :=
  {q : List E // Multidigraph.IsDipath G.src G.tgt (G.source i) (G.sink i) q}

/-- Underlying arc list of a player's simple path. -/
@[expose] def Path.arcs {G : FairConnectionGame ι V E} {i : ι} (p : G.Path i) : List E :=
  p.1

/-- `Path.arcs p` is a valid simple dipath from `G.source i` to `G.sink i`. -/
theorem Path.isDipath {G : FairConnectionGame ι V E} {i : ι} (p : G.Path i) :
    Multidigraph.IsDipath G.src G.tgt (G.source i) (G.sink i) (Path.arcs p) :=
  p.2

/-- Every strategy path uses each arc at most once. -/
theorem Path.nodup {G : FairConnectionGame ι V E} {i : ι} (p : G.Path i) :
    (Path.arcs p).Nodup :=
  p.isDipath.nodup

/-- Finite set of edges traversed by the path `p`. -/
@[expose] def pathEdges [DecidableEq E] {i : ι} (p : G.Path i) : Finset E :=
  (Path.arcs p).toFinset

@[simp]
theorem mem_pathEdges_iff [DecidableEq E] {i : ι} {p : G.Path i} {e : E} :
    e ∈ G.pathEdges p ↔ e ∈ Path.arcs p :=
  List.mem_toFinset

instance instFinitePath [Finite E] (i : ι) : Finite (G.Path i) :=
  letI := Fintype.ofFinite E
  Finite.of_injective (fun p : G.Path i => (⟨Path.arcs p, Path.nodup p⟩ : {l : List E // l.Nodup}))
    fun _ _ h => Subtype.ext (congrArg (Subtype.val : {l : List E // l.Nodup} → List E) h)

/-- Every player's sink terminal is reachable from its source terminal by a simple directed path. -/
@[expose] def TerminalsConnected : Prop :=
  ∀ i, ∃ q, Multidigraph.IsDipath G.src G.tgt (G.source i) (G.sink i) q

theorem terminalsConnected_iff_nonempty :
    G.TerminalsConnected ↔ ∀ i, Nonempty (G.Path i) :=
  forall_congr' fun _ => nonempty_subtype.symm

theorem terminalsConnected_iff_reflTransGen :
    G.TerminalsConnected ↔
      ∀ i, Relation.ReflTransGen (Multidigraph.toDigraph G.src G.tgt).Adj
        (G.source i) (G.sink i) :=
  forall_congr' fun _ => Multidigraph.exists_isDipath_iff_reflTransGen

/-- `F` is a **centralized Steiner subnetwork** of `G` if for every player `i`, `F` contains the
arcs of a simple directed path from `G.source i` to `G.sink i`. -/
@[expose] def IsSteinerSubgraph (F : Finset E) : Prop :=
  ∀ i, ∃ q, Multidigraph.IsDipath G.src G.tgt (G.source i) (G.sink i) q ∧ ∀ e ∈ q, e ∈ F

theorem IsSteinerSubgraph.terminalsConnected {F : Finset E} (hF : G.IsSteinerSubgraph F) :
    G.TerminalsConnected :=
  fun i => let ⟨q, hq, _⟩ := hF i; ⟨q, hq⟩

/-- Embedding of `G` as a fair cost-sharing atomic congestion game on edge sets
([TardosWexler2007], Section 19.3.2). -/
@[expose] noncomputable def toCongestionGame [DecidableEq E] : CongestionGame ι G.Path E :=
  CongestionGame.fairCostSharing (fun _ p => G.pathEdges p) G.edgeCost

/-- Strategic cost-minimization game of `G` under Shapley equal cost sharing `c_e / k_e`. -/
@[expose] noncomputable def toCostGame [Fintype ι] [DecidableEq E] : CostGame ι G.Path :=
  G.toCongestionGame.toCostGame

/-- Number `k_e(s)` of players whose chosen paths traverse edge `e` at profile `s`. -/
@[expose] def edgeLoad [Fintype ι] [DecidableEq E] (s : ∀ i, G.Path i) (e : E) : ℕ :=
  (Finset.univ.filter fun i => e ∈ G.pathEdges (s i)).card

@[simp]
theorem toCongestionGame_load [Fintype ι] [DecidableEq E] (s : ∀ i, G.Path i) (e : E) :
    G.toCongestionGame.load s e = G.edgeLoad s e := by
  simp [toCongestionGame, CongestionGame.load, edgeLoad]

/-- **Shapley equal cost-sharing formula**: player `i` pays `∑ e ∈ pathEdges (s i), c_e / k_e(s)`.
-/
theorem toCostGame_cost [Fintype ι] [DecidableEq E] (i : ι) (s : ∀ i, G.Path i) :
    G.toCostGame.cost i s = ∑ e ∈ G.pathEdges (s i), G.edgeCost e / G.edgeLoad s e := by
  simp [toCostGame, toCongestionGame, CongestionGame.toCostGame_cost, CongestionGame.load,
    edgeLoad]

/-- Subnetwork `⋃ i, pathEdges (s i)` formed by the players' chosen paths at profile `s`. -/
@[expose] def formedEdges [Fintype ι] [DecidableEq E] (s : ∀ i, G.Path i) : Finset E :=
  Finset.univ.biUnion fun i => G.pathEdges (s i)

theorem mem_formedEdges_iff [Fintype ι] [DecidableEq E] {s : ∀ i, G.Path i} {e : E} :
    e ∈ G.formedEdges s ↔ 0 < G.edgeLoad s e := by
  rw [formedEdges, Finset.mem_biUnion, edgeLoad, Finset.card_pos]
  exact ⟨fun ⟨i, hi, he⟩ => ⟨i, Finset.mem_filter.2 ⟨hi, he⟩⟩,
    fun ⟨i, hi⟩ => ⟨i, (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩⟩

theorem isSteinerSubgraph_formedEdges [Fintype ι] [DecidableEq E] (s : ∀ i, G.Path i) :
    G.IsSteinerSubgraph (G.formedEdges s) :=
  fun i => ⟨Path.arcs (s i), Path.isDipath (s i), fun _ he =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, (G.mem_pathEdges_iff).2 he⟩⟩

/-- **Social cost is the total cost of the formed subnetwork**: summing all players' equal cost
shares cancels `k_e(s)` on every used edge, leaving `∑ e ∈ formedEdges s, edgeCost e`. -/
theorem socialCost_eq_sum_formedEdges [Fintype ι] [DecidableEq E] (s : ∀ i, G.Path i) :
    G.toCostGame.socialCost s = ∑ e ∈ G.formedEdges s, G.edgeCost e :=
  CongestionGame.socialCost_fairCostSharing_biUnion (fun _ p => G.pathEdges p) G.edgeCost s

/-- Every centralized Steiner subnetwork `F` induces a path profile `s` with `formedEdges s ⊆ F`
and (for nonnegative edge costs) `socialCost s ≤ ∑ e ∈ F, edgeCost e`. -/
theorem exists_profile_socialCost_le_steinerCost [Fintype ι] [DecidableEq E]
    (hc : ∀ e, 0 ≤ G.edgeCost e) {F : Finset E} (hF : G.IsSteinerSubgraph F) :
    ∃ s : ∀ i, G.Path i,
      G.formedEdges s ⊆ F ∧ G.toCostGame.socialCost s ≤ ∑ e ∈ F, G.edgeCost e := by
  let s : ∀ i, G.Path i := fun i => ⟨(hF i).choose, (hF i).choose_spec.1⟩
  have hsub : G.formedEdges s ⊆ F := fun e he =>
    let ⟨i, _, hi⟩ := Finset.mem_biUnion.1 he
    (hF i).choose_spec.2 e ((G.mem_pathEdges_iff).1 hi)
  exact ⟨s, hsub, (G.socialCost_eq_sum_formedEdges s).trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hc e)⟩

end Basic

/-! ### Rosenthal's harmonic potential, pure Nash equilibria, PoS ≤ H_k, and PoA ≤ k -/

section PotentialAndEfficiency

variable [Fintype ι] [DecidableEq E] (G : FairConnectionGame ι V E)

/-- **Rosenthal's harmonic potential** of `G`: `Φ s = ∑ e, edgeCost e * H (edgeLoad s e)`
([Rosenthal1973]; [TardosWexler2007], Section 19.3.1). -/
noncomputable def potential [Fintype E] (s : ∀ i, G.Path i) : ℝ :=
  G.toCongestionGame.rosenthalPotential s

theorem potential_eq [Fintype E] (s : ∀ i, G.Path i) :
    G.potential s = ∑ e, G.edgeCost e * harmonic (G.edgeLoad s e) := by
  rw [potential, toCongestionGame, CongestionGame.rosenthalPotential_fairCostSharing]
  exact Finset.sum_congr rfl fun e _ => by rw [← G.toCongestionGame_load, toCongestionGame]

/-- **Every finite fair connection game is an exact potential game** ([TardosWexler2007],
Lemma 19.7): a unilateral path change by player `i` changes `G.potential` by the exact change in
player `i`'s cost. -/
theorem isExactPotential_potential [DecidableEq ι] [Fintype E] :
    G.toCostGame.IsExactPotential G.potential :=
  G.toCongestionGame.isExactPotential_rosenthalPotential

/-- **Potential lower bound** ([TardosWexler2007], Lemma 19.8, first inequality): with nonnegative
edge costs, `socialCost s ≤ potential s`. -/
theorem socialCost_le_potential [Fintype E] (hc : ∀ e, 0 ≤ G.edgeCost e) (s : ∀ i, G.Path i) :
    G.toCostGame.socialCost s ≤ G.potential s :=
  CongestionGame.socialCost_le_rosenthalPotential_fairCostSharing _ _ hc s

/-- **Potential upper bound** ([TardosWexler2007], Lemma 19.8, second inequality): with nonnegative
edge costs and `k = Fintype.card ι` players, `potential s ≤ H k * socialCost s`. -/
theorem potential_le_harmonic_mul_socialCost [Fintype E] (hc : ∀ e, 0 ≤ G.edgeCost e)
    (s : ∀ i, G.Path i) :
    G.potential s ≤ harmonic (Fintype.card ι) * G.toCostGame.socialCost s :=
  CongestionGame.rosenthalPotential_fairCostSharing_le_harmonic_mul _ _ hc s

/-- **Finite improvement property** ([TardosWexler2007], Section 19.3.1): on a finite edge set,
every sequence of strictly improving unilateral path deviations is finite. -/
theorem hasFIP [DecidableEq ι] [Finite E] : G.toCostGame.HasFIP :=
  G.toCongestionGame.hasFIP

/-- **Pure Nash equilibrium existence** ([TardosWexler2007], Section 19.3.1): every fair
connection game on finitely many edges in which each player's sink is reachable from its source
admits a pure Nash equilibrium. -/
theorem exists_isPureNash [DecidableEq ι] [Finite E] (hconn : G.TerminalsConnected) :
    ∃ s, G.toCostGame.IsPureNash s :=
  have := (G.terminalsConnected_iff_nonempty).1 hconn
  G.toCongestionGame.exists_isPureNash

/-- **Anshelevich et al. `H_k` price-of-stability theorem** ([AnshelevichDKTWR2008];
[TardosWexler2007], Theorem 19.10): in a `k`-player fair connection game (`k = Fintype.card ι`) on
finitely many edges with nonnegative edge costs and connected terminal pairs, there exists a pure
Nash equilibrium `s` (a global minimizer of Rosenthal's potential) with
`socialCost s ≤ H k * socialCost s'` for every strategy profile `s'`. -/
theorem exists_isPureNash_socialCost_le_harmonic_mul [DecidableEq ι] [Finite E]
    (hconn : G.TerminalsConnected) (hc : ∀ e, 0 ≤ G.edgeCost e) :
    ∃ s, G.toCostGame.IsPureNash s ∧
      ∀ s', G.toCostGame.socialCost s ≤ harmonic (Fintype.card ι) * G.toCostGame.socialCost s' :=
  have := (G.terminalsConnected_iff_nonempty).1 hconn
  CongestionGame.exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul _ _ hc

/-- **Anshelevich et al. `H_k` theorem against centralized Steiner subnetworks**
([AnshelevichDKTWR2008]; [TardosWexler2007], Theorem 19.10): when at least one Steiner subnetwork
exists (equivalently `G.TerminalsConnected`), there exists a pure Nash equilibrium `s` whose formed
network costs at most `H k` times `∑ e ∈ F, edgeCost e` for **every** centralized Steiner
subnetwork `F : Finset E`. -/
theorem exists_isPureNash_socialCost_le_harmonic_mul_steinerCost [DecidableEq ι] [Finite E]
    (hconn : G.TerminalsConnected) (hc : ∀ e, 0 ≤ G.edgeCost e) :
    ∃ s, G.toCostGame.IsPureNash s ∧
      ∀ F, G.IsSteinerSubgraph F →
        G.toCostGame.socialCost s ≤ harmonic (Fintype.card ι) * ∑ e ∈ F, G.edgeCost e := by
  obtain ⟨s, hs, hle⟩ := G.exists_isPureNash_socialCost_le_harmonic_mul hconn hc
  refine ⟨s, hs, fun F hF => ?_⟩
  obtain ⟨s', -, hs'⟩ := G.exists_profile_socialCost_le_steinerCost hc hF
  exact (hle s').trans (mul_le_mul_of_nonneg_left hs' (by exact_mod_cast harmonic_nonneg _))

/-- **Better-response dynamics from any profile reach an `H_k`-competitive pure Nash equilibrium**
([TardosWexler2007], Section 19.3.1 and Theorem 19.10): started at a socially optimal profile,
improving unilateral path deviations terminate at a pure Nash equilibrium within factor `H k` of
`OPT`. -/
theorem exists_reflTransGen_isPureNash_socialCost_le_harmonic_mul [DecidableEq ι] [Finite E]
    (hc : ∀ e, 0 ≤ G.edgeCost e) (s₀ : ∀ i, G.Path i) :
    ∃ t, Relation.ReflTransGen (flip G.toCostGame.Improves) s₀ t ∧
      G.toCostGame.IsPureNash t ∧
      G.toCostGame.socialCost t ≤ harmonic (Fintype.card ι) * G.toCostGame.socialCost s₀ :=
  CongestionGame.exists_reflTransGen_isPureNash_fairCostSharing_socialCost_le_harmonic_mul _ _ hc s₀

/-- **`(k, 0)`-smoothness of fair connection games** ([Roughgarden2015], Definition 2.1;
[TardosWexler2007], Section 19.3). -/
theorem isSmooth [DecidableEq ι] [Finite E] (hc : ∀ e, 0 ≤ G.edgeCost e) :
    G.toCostGame.IsSmooth (Fintype.card ι) 0 :=
  CongestionGame.isSmooth_fairCostSharing _ _ hc

/-- **Price of anarchy at most `k`** ([Roughgarden2015], Theorem 3.2; [TardosWexler2007],
Section 19.3): every pure Nash equilibrium `s` of a `k`-player fair connection game with nonnegative
edge costs satisfies `socialCost s ≤ k * socialCost s'` for every profile `s'`. -/
theorem socialCost_le_card_mul_of_isPureNash [DecidableEq ι] [Finite E]
    (hc : ∀ e, 0 ≤ G.edgeCost e) {s : ∀ i, G.Path i} (hs : G.toCostGame.IsPureNash s)
    (s' : ∀ i, G.Path i) :
    G.toCostGame.socialCost s ≤ Fintype.card ι * G.toCostGame.socialCost s' :=
  CongestionGame.socialCost_fairCostSharing_le_card_mul_of_isPureNash _ _ hc hs s'

/-- **Price of anarchy at most `k` against centralized Steiner subnetworks**: every pure Nash
equilibrium `s` costs at most `k * ∑ e ∈ F, edgeCost e` for every Steiner subnetwork `F`. -/
theorem socialCost_le_card_mul_steinerCost_of_isPureNash [DecidableEq ι] [Finite E]
    (hc : ∀ e, 0 ≤ G.edgeCost e) {s : ∀ i, G.Path i} (hs : G.toCostGame.IsPureNash s)
    {F : Finset E} (hF : G.IsSteinerSubgraph F) :
    G.toCostGame.socialCost s ≤ Fintype.card ι * ∑ e ∈ F, G.edgeCost e := by
  obtain ⟨s', -, hs'⟩ := G.exists_profile_socialCost_le_steinerCost hc hF
  exact (G.socialCost_le_card_mul_of_isPureNash hc hs s').trans
    (mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg _))

end PotentialAndEfficiency

end FairConnectionGame

/-! ### Undirected Fair Connection Games -/

/-- A **fair connection game on an undirected simple graph** `graph : SimpleGraph V`
([AnshelevichDKTWR2008]; [RoughgardenTardos2007]): each undirected edge `e : Sym2 V` has cost
`edgeCost e`, and each player `i : ι` chooses a simple undirected path in `graph` between
`source i` and `sink i`. Players traversing the same unordered edge `s(u, v)` in either
direction share its cost equally. -/
structure UndirectedFairConnectionGame (ι V : Type*) where
  /-- Underlying undirected graph. -/
  graph : SimpleGraph V
  /-- Fixed construction cost `c_e` of unordered edge `e : Sym2 V`. -/
  edgeCost : Sym2 V → ℝ
  /-- Source terminal `s_i` of player `i`. -/
  source : ι → V
  /-- Sink terminal `t_i` of player `i`. -/
  sink : ι → V

namespace UndirectedFairConnectionGame

variable {ι V : Type*} (G : UndirectedFairConnectionGame ι V)

/-- Strategy of player `i` in `G`: a simple undirected path in `G.graph` from `G.source i` to
`G.sink i`. -/
abbrev Path (i : ι) : Type _ :=
  G.graph.Path (G.source i) (G.sink i)

/-- Finite set of unordered edges `Sym2 V` traversed by an undirected simple path `p`. -/
@[expose] def pathEdges [DecidableEq V] {i : ι} (p : G.Path i) : Finset (Sym2 V) :=
  (p : G.graph.Walk (G.source i) (G.sink i)).edges.toFinset

@[simp]
theorem mem_pathEdges_iff [DecidableEq V] {i : ι} {p : G.Path i} {e : Sym2 V} :
    e ∈ G.pathEdges p ↔ e ∈ (p : G.graph.Walk (G.source i) (G.sink i)).edges :=
  List.mem_toFinset

instance instFinitePath [Finite V] (i : ι) : Finite (G.Path i) :=
  letI := Fintype.ofFinite V
  Finite.of_injective
    (fun p : G.Path i =>
      (⟨(p : G.graph.Walk (G.source i) (G.sink i)).support, p.nodup_support⟩ :
        {l : List V // l.Nodup}))
    fun _ _ h => Subtype.ext (SimpleGraph.Walk.support_injective
      (congrArg (Subtype.val : {l : List V // l.Nodup} → List V) h))

/-- Every player's source and sink terminals lie in the same connected component of `G.graph`. -/
@[expose] def TerminalsConnected : Prop :=
  ∀ i, G.graph.Reachable (G.source i) (G.sink i)

theorem terminalsConnected_iff_nonempty :
    G.TerminalsConnected ↔ ∀ i, Nonempty (G.Path i) :=
  forall_congr' fun _ =>
    ⟨fun h => let ⟨p, hp⟩ := h.exists_isPath; ⟨⟨p, hp⟩⟩, fun ⟨⟨p, _⟩⟩ => p.reachable⟩

/-- Embedding of `G` into `CongestionGame.fairCostSharing` on unordered edges `Sym2 V`. -/
@[expose] noncomputable def toCongestionGame [DecidableEq V] : CongestionGame ι G.Path (Sym2 V) :=
  CongestionGame.fairCostSharing (fun _ p => G.pathEdges p) G.edgeCost

/-- Strategic cost-minimization game of `G` under Shapley equal cost sharing. -/
@[expose] noncomputable def toCostGame [Fintype ι] [DecidableEq V] : CostGame ι G.Path :=
  G.toCongestionGame.toCostGame

/-- Number `k_e(s)` of players whose undirected paths traverse edge `e : Sym2 V`. -/
@[expose] def edgeLoad [Fintype ι] [DecidableEq V] (s : ∀ i, G.Path i) (e : Sym2 V) : ℕ :=
  (Finset.univ.filter fun i => e ∈ G.pathEdges (s i)).card

theorem toCostGame_cost [Fintype ι] [DecidableEq V] (i : ι) (s : ∀ i, G.Path i) :
    G.toCostGame.cost i s = ∑ e ∈ G.pathEdges (s i), G.edgeCost e / G.edgeLoad s e := by
  simp [toCostGame, toCongestionGame, CongestionGame.toCostGame_cost, CongestionGame.load,
    edgeLoad]

/-- Subnetwork `⋃ i, pathEdges (s i)` of unordered edges formed at profile `s`. -/
@[expose] def formedEdges [Fintype ι] [DecidableEq V] (s : ∀ i, G.Path i) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i => G.pathEdges (s i)

theorem socialCost_eq_sum_formedEdges [Fintype ι] [DecidableEq V] (s : ∀ i, G.Path i) :
    G.toCostGame.socialCost s = ∑ e ∈ G.formedEdges s, G.edgeCost e :=
  CongestionGame.socialCost_fairCostSharing_biUnion (fun _ p => G.pathEdges p) G.edgeCost s

/-- Rosenthal's harmonic potential on undirected edges `Sym2 V`. -/
noncomputable def potential [Fintype ι] [DecidableEq V] [Fintype V] (s : ∀ i, G.Path i) : ℝ :=
  G.toCongestionGame.rosenthalPotential s

theorem potential_eq [Fintype ι] [DecidableEq V] [Fintype V] (s : ∀ i, G.Path i) :
    G.potential s = ∑ e : Sym2 V, G.edgeCost e * harmonic (G.edgeLoad s e) := by
  rw [potential, toCongestionGame, CongestionGame.rosenthalPotential_fairCostSharing]
  exact Finset.sum_congr rfl fun e _ => by
    simp only [CongestionGame.load, CongestionGame.fairCostSharing_resources, edgeLoad]

theorem isExactPotential_potential [Fintype ι] [DecidableEq ι] [DecidableEq V] [Fintype V] :
    G.toCostGame.IsExactPotential G.potential :=
  G.toCongestionGame.isExactPotential_rosenthalPotential

theorem exists_isPureNash [Fintype ι] [DecidableEq ι] [DecidableEq V] [Finite V]
    (hconn : G.TerminalsConnected) :
    ∃ s, G.toCostGame.IsPureNash s :=
  have := (G.terminalsConnected_iff_nonempty).1 hconn
  G.toCongestionGame.exists_isPureNash

theorem exists_isPureNash_socialCost_le_harmonic_mul [Fintype ι] [DecidableEq ι] [DecidableEq V]
    [Finite V] (hconn : G.TerminalsConnected) (hc : ∀ e, 0 ≤ G.edgeCost e) :
    ∃ s, G.toCostGame.IsPureNash s ∧
      ∀ s', G.toCostGame.socialCost s ≤ harmonic (Fintype.card ι) * G.toCostGame.socialCost s' :=
  have := (G.terminalsConnected_iff_nonempty).1 hconn
  CongestionGame.exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul _ _ hc

theorem socialCost_le_card_mul_of_isPureNash [Fintype ι] [DecidableEq ι] [DecidableEq V] [Finite V]
    (hc : ∀ e, 0 ≤ G.edgeCost e) {s : ∀ i, G.Path i} (hs : G.toCostGame.IsPureNash s)
    (s' : ∀ i, G.Path i) :
    G.toCostGame.socialCost s ≤ Fintype.card ι * G.toCostGame.socialCost s' :=
  CongestionGame.socialCost_fairCostSharing_le_card_mul_of_isPureNash _ _ hc hs s'

end UndirectedFairConnectionGame

end Cslib.GameTheory
