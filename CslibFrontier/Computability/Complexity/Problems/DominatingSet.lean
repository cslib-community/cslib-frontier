/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.NatCodec
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DominatingSet
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Dominating sets

`DominatingSet` is problem GT2 of [Garey and Johnson][GareyJohnson1979]. Its instances
(`Cslib.Complexity.DominatingSetInstance`, encoded by `Cslib.Complexity.encDominatingSet`) pair a
graph, given by a list of vertices and a list of edges, with a number `k`. An instance is in the
problem when some `k` declared vertices dominate the graph: every declared vertex is chosen or is
adjacent to a chosen one. Graphs are read on their declared vertices through
`Cslib.Complexity.Graph.induced`, and domination through `SimpleGraph.IsDominatingSet`, as for
`VertexCover`. Edges with an undeclared endpoint and self-loops are therefore ignored, and
repeated vertex entries count once.

The dominating set has exactly `k` distinct vertices, matching `VertexCover` and
`IndependentSet`. A set of declared vertices containing a dominating set is dominating, so this
agrees with the textbook formulation "a dominating set of at most `k` vertices" for every `k` up to
the number `n` of distinct declared vertices. `DominatingSet` rejects every `k > n`
(`mem_DominatingSet_iff_exists_card_le`).

`NP` membership uses a subset witness (`Cslib.Complexity.mem_NP_of_subsetWitness`): the certificate
selects declared vertices, and `DominatingSet.isDominating` checks domination.

## The reduction from vertex cover

`VertexCover.toDominatingSet` maps `(G, k)` to `⟨VertexCover.dominationGraph G, k + 1⟩`. The graph
`dominationGraph G` has:

* a copy `2v` of every declared vertex `v` of `G`;
* a hub `1` adjacent to every copy, and a pendant `3` adjacent only to the hub;
* for every edge `e` of `G` between distinct declared vertices (`VertexCover.properEdges`), a
  vertex `VertexCover.edgeVertex e = 2 * Nat.pair e.1 e.2 + 5` adjacent to the copies of the two
  endpoints of `e`.

The hub dominates every copy, and either the hub or the pendant must be chosen to dominate the
pendant. Choosing the hub costs one vertex. The vertex of an edge is then dominated exactly when
an endpoint's copy, or the edge's own vertex, is chosen. Replacing the vertex of an edge by an
endpoint reads a dominating set of `k + 1` vertices back as a vertex cover of at most `k` vertices,
and a vertex cover of `k` vertices with the hub is a dominating set of `k + 1` vertices. Since
`VertexCover` asks for exactly `k` vertices, instances with `k > n` are sent to the target `0`. No
dominating set of `0` vertices dominates the hub.

Garey and Johnson cite a transformation from VERTEX COVER for GT2 (locator from secondary
sources). The common textbook version
keeps the edges of `G`, adds a vertex for every edge and keeps `k`, but it must account separately
for isolated vertices of `G`: they impose nothing on a cover and must be chosen in a dominating set.
The hub and pendant used here dominate every copy, including isolated ones, at a fixed cost of one
vertex. So the reduction needs neither the number of isolated vertices nor the edges of `G`
between copies.

## Main definitions

* `Cslib.Complexity.DominatingSetInstance`, `Cslib.Complexity.encDominatingSet`.
* `Cslib.Complexity.DominatingSet`.
* `Cslib.Complexity.DominatingSet.isDominating`: the executable domination test.
* `Cslib.Complexity.VertexCover.vertexCodec`, `Cslib.Complexity.VertexCover.edgeVertex`,
  `Cslib.Complexity.VertexCover.dominationGraph`, `Cslib.Complexity.VertexCover.toDominatingSet`:
  the reduction from `VertexCover`.

## Main results

* `Cslib.Complexity.mem_DominatingSet_iff`, `Cslib.Complexity.mem_DominatingSet_iff_exists_card_le`:
  dominating sets of exactly `k` vertices versus dominating sets of at most `k` vertices.
* `Cslib.Complexity.DominatingSet.isDominating_eq_true_iff`,
  `Cslib.Complexity.DominatingSet.computableInPolyTime_isDominating`,
  `Cslib.Complexity.DominatingSet.mem_NP`: `DominatingSet ∈ NP encDominatingSet`.
* `Cslib.Complexity.VertexCover.toDominatingSet_mem_iff`,
  `Cslib.Complexity.VertexCover.computableInPolyTime_toDominatingSet`,
  `Cslib.Complexity.polyTimeReducible_VertexCover_DominatingSet`: the reduction.
* `Cslib.Complexity.DominatingSet_npHard`, `Cslib.Complexity.DominatingSet_npComplete`:
  `DominatingSet` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979], Problem GT2.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(graph, bound)` of **Dominating Set**. -/
@[ext]
structure DominatingSetInstance where
  /-- The undirected graph to dominate. -/
  graph : Graph
  /-- The number of vertices in the dominating set. -/
  bound : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `DominatingSetInstance` as a pair `(graph, bound)`. -/
enc_structure encDominatingSet : DominatingSetInstance where
  graph : encGraph,
  bound : encNat

attribute [fun_prop] encDominatingSet_graph_polyTime encDominatingSet_bound_polyTime
  encDominatingSet_mk_polyTime

/-- The graphs with a dominating set of `k` of their vertices [Garey and Johnson, Problem
GT2][GareyJohnson1979]: `k` declared vertices such that every declared vertex is chosen or adjacent
to a chosen one. -/
@[expose]
def DominatingSet : Set DominatingSetInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices},
    x.graph.induced.IsDominatingSet S ∧ S.card = x.bound}

/-- Membership in `DominatingSet` as a finite set of `k` declared vertices such that every declared
vertex is chosen or adjacent to a chosen one. -/
@[simp]
theorem mem_DominatingSet_iff {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : DominatingSetInstance) ∈ DominatingSet ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
        (∀ v ∈ G.vertices, v ∈ S ∨ ∃ s ∈ S, G.toSimpleGraph.Adj v s) ∧ S.card = k := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    refine ⟨S.map (.subtype _),
      fun v hv => by obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hv; exact u.2,
      fun v hv => (SimpleGraph.isDominatingSet_iff.1 hS ⟨v, hv⟩).imp (Finset.mem_map_of_mem _)
        fun ⟨s, hs, hadj⟩ => ⟨s.1, Finset.mem_map_of_mem (.subtype _) hs, hadj⟩,
      (Finset.card_map _).trans hcard⟩
  · rintro ⟨S, hSV, hS, rfl⟩
    refine ⟨S.subtype (· ∈ G.vertices), SimpleGraph.isDominatingSet_iff.2 fun v =>
        (hS v.1 v.2).imp (fun h => Finset.mem_coe.2 (Finset.mem_subtype.2 h))
          fun ⟨s, hs, hadj⟩ => ⟨⟨s, hSV s hs⟩, Finset.mem_coe.2 (Finset.mem_subtype.2 hs), hadj⟩,
      by rw [← Finset.card_map (.subtype _), Finset.subtype_map, Finset.filter_eq_self.mpr hSV]⟩

/-- `DominatingSet` through dominating sets of at most `k` vertices: `(G, k) ∈ DominatingSet`
exactly when `k` is at most the number of distinct declared vertices and some dominating set has
at most `k` vertices. -/
theorem mem_DominatingSet_iff_exists_card_le {G : Graph} {k : ℕ} :
    (⟨G, k⟩ : DominatingSetInstance) ∈ DominatingSet ↔
      k ≤ G.vertices.toFinset.card ∧ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧
        (∀ v ∈ G.vertices, v ∈ S ∨ ∃ s ∈ S, G.toSimpleGraph.Adj v s) ∧ S.card ≤ k := by
  rw [mem_DominatingSet_iff]
  constructor
  · rintro ⟨S, hSV, hS, rfl⟩
    exact ⟨Finset.card_le_card fun v hv => List.mem_toFinset.2 (hSV v hv), S, hSV, hS, le_rfl⟩
  · rintro ⟨hk, S, hSV, hS, hcard⟩
    obtain ⟨T, hST, hTV, hT⟩ := Finset.exists_subsuperset_card_eq
      (fun v hv => List.mem_toFinset.2 (hSV v hv)) hcard hk
    refine ⟨T, fun v hv => List.mem_toFinset.1 (hTV hv), fun v hv => ?_, hT⟩
    exact (hS v hv).imp (@hST v) fun ⟨s, hs, hadj⟩ => ⟨s, hST hs, hadj⟩

namespace DominatingSet

/-! ### Membership in `NP` -/

/-- Whether every declared vertex of `G` is in `C` or adjacent to a vertex of `C`. -/
@[expose]
def isDominating (G : Graph) (C : List ℕ) : Bool :=
  G.vertices.all fun v => decide (v ∈ C) || C.any fun s => G.adjBool v s

/-- `isDominating G C` holds exactly when `C` dominates the declared vertices of `G`. -/
theorem isDominating_eq_true_iff {G : Graph} {C : List ℕ} :
    isDominating G C = true ↔ ∀ v ∈ G.vertices, v ∈ C ∨ ∃ s ∈ C, G.toSimpleGraph.Adj v s := by
  simp only [isDominating, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Graph.adjBool_eq_true_iff]

/-- The domination test is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isDominating :
    ComputableInPolyTime (fun p : Graph × List ℕ => isDominating p.1 p.2)
      (encPair encGraph (encList encNat)) encBool := by
  unfold isDominating
  fun_prop

/-- `DominatingSet` belongs to `NP`: the certificate selects distinct declared vertices, and the
verifier checks their number and `isDominating`. -/
theorem mem_NP : DominatingSet ∈ NP encDominatingSet := by
  have hset : DominatingSet = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      ((∀ v ∈ x.graph.vertices, v ∈ S ∨ ∃ s ∈ S, x.graph.toSimpleGraph.Adj v s) ∧
        S.card = x.bound)} :=
    Set.ext fun ⟨_, _⟩ => mem_DominatingSet_iff
  rw [hset]
  refine mem_NP_of_subsetWitness (encγ := encNat)
    (vs := fun x : DominatingSetInstance => x.graph.vertices)
    (check := fun y => decide (y.2.length = y.1.bound) && isDominating y.1.graph y.2)
    (by fun_prop)
    (by fun_prop) fun x l hl _ => ?_
  · simp only [Bool.and_eq_true, decide_eq_true_eq, isDominating_eq_true_iff, List.mem_toFinset,
      List.toFinset_card_of_nodup hl, and_comm]

end DominatingSet

/-! ### Reduction from vertex covers -/

namespace VertexCover

/-- Codec partitioning the vertices of `dominationGraph G` into copies of declared vertices
(`.inl v = 2 * v`), the hub and pendant (`.inr (.inl 0) = 1` and `.inr (.inl 1) = 3`), and proper
edges (`.inr (.inr e) = 2 * (Nat.pair e.1 e.2 + 2) + 1`). -/
@[expose]
def vertexCodec : NatCodec (ℕ ⊕ (Fin 2 ⊕ (ℕ × ℕ))) :=
  NatCodec.nat.sum ((NatCodec.nat.pair .nat).finSum 2)

/-- The vertex of the edge `e` in `dominationGraph`: `vertexCodec (.inr (.inr e))`. -/
@[expose]
def edgeVertex (e : ℕ × ℕ) : ℕ :=
  vertexCodec (.inr (.inr e))

/-- Distinct edges have distinct vertices. -/
theorem edgeVertex_injective : Function.Injective edgeVertex :=
  fun _ _ h => Sum.inr.inj (Sum.inr.inj (vertexCodec.injective h))

/-- The graph of the reduction from `VertexCover` to `DominatingSet`: a copy `2v` of every
declared vertex `v`, a hub `1` adjacent to every copy, a pendant `3` adjacent to the hub, and for
every proper edge `e` a vertex `edgeVertex e` adjacent to the copies of the endpoints of `e`. -/
@[expose]
def dominationGraph (G : Graph) : Graph :=
  ⟨1 :: 3 :: G.vertices.map (2 * ·) ++ (properEdges G).map edgeVertex,
    (1, 3) :: G.vertices.map (fun v => (1, 2 * v)) ++
      (properEdges G).flatMap fun e => [(edgeVertex e, 2 * e.1), (edgeVertex e, 2 * e.2)]⟩

/-- The vertices of `dominationGraph G`. -/
theorem mem_dominationGraph_fst {G : Graph} {w : ℕ} :
    w ∈ (dominationGraph G).vertices ↔ w = 1 ∨ w = 3 ∨ (∃ v ∈ G.vertices, 2 * v = w) ∨
      ∃ e ∈ properEdges G, edgeVertex e = w := by
  simp only [dominationGraph, List.mem_append, List.mem_cons, List.mem_map, or_assoc]

/-- The edges of `dominationGraph G`. -/
theorem mem_dominationGraph_snd {G : Graph} {a b : ℕ} :
    (a, b) ∈ (dominationGraph G).edges ↔ (a = 1 ∧ b = 3) ∨
      (a = 1 ∧ ∃ v ∈ G.vertices, b = 2 * v) ∨
      ∃ e ∈ properEdges G, a = edgeVertex e ∧ (b = 2 * e.1 ∨ b = 2 * e.2) := by
  simp only [dominationGraph, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    Prod.mk.injEq, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩) | ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    exacts [Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, v, hv, rfl⟩),
      Or.inr (Or.inr ⟨e, he, rfl, Or.inl rfl⟩), Or.inr (Or.inr ⟨e, he, rfl, Or.inr rfl⟩)]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, v, hv, rfl⟩ | ⟨e, he, rfl, rfl | rfl⟩)
    exacts [Or.inl (Or.inl ⟨rfl, rfl⟩), Or.inl (Or.inr ⟨v, hv, rfl, rfl⟩),
      Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩, Or.inr ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩]

private theorem edgeVertex_ne_one (e : ℕ × ℕ) : edgeVertex e ≠ 1 :=
  show vertexCodec (.inr (.inr e)) ≠ vertexCodec (.inr (.inl 0)) from
    vertexCodec.injective.ne (by simp)

private theorem edgeVertex_ne_three (e : ℕ × ℕ) : edgeVertex e ≠ 3 :=
  show vertexCodec (.inr (.inr e)) ≠ vertexCodec (.inr (.inl 1)) from
    vertexCodec.injective.ne (by simp)

private theorem edgeVertex_ne_double (e : ℕ × ℕ) (v : ℕ) : edgeVertex e ≠ 2 * v :=
  show vertexCodec (.inr (.inr e)) ≠ vertexCodec (.inl v) from
    vertexCodec.injective.ne (by simp)

private theorem double_ne_one (v : ℕ) : 2 * v ≠ 1 :=
  show vertexCodec (.inl v) ≠ vertexCodec (.inr (.inl 0)) from
    vertexCodec.injective.ne (by simp)

private theorem double_ne_three (v : ℕ) : 2 * v ≠ 3 :=
  show vertexCodec (.inl v) ≠ vertexCodec (.inr (.inl 1)) from
    vertexCodec.injective.ne (by simp)

private theorem adj_three_one (G : Graph) : (dominationGraph G).toSimpleGraph.Adj 3 1 :=
  Graph.toSimpleGraph_adj.2 ⟨by decide, Or.inr (mem_dominationGraph_snd.2 (Or.inl ⟨rfl, rfl⟩))⟩

private theorem adj_double_one {G : Graph} {v : ℕ} (hv : v ∈ G.vertices) :
    (dominationGraph G).toSimpleGraph.Adj (2 * v) 1 :=
  Graph.toSimpleGraph_adj.2 ⟨double_ne_one v,
    Or.inr (mem_dominationGraph_snd.2 (Or.inr (Or.inl ⟨rfl, v, hv, rfl⟩)))⟩

private theorem adj_edgeVertex_fst {G : Graph} {e : ℕ × ℕ} (he : e ∈ properEdges G) :
    (dominationGraph G).toSimpleGraph.Adj (edgeVertex e) (2 * e.1) :=
  Graph.toSimpleGraph_adj.2 ⟨edgeVertex_ne_double e e.1,
    Or.inl (mem_dominationGraph_snd.2 (Or.inr (Or.inr ⟨e, he, rfl, Or.inl rfl⟩)))⟩

private theorem adj_edgeVertex_snd {G : Graph} {e : ℕ × ℕ} (he : e ∈ properEdges G) :
    (dominationGraph G).toSimpleGraph.Adj (edgeVertex e) (2 * e.2) :=
  Graph.toSimpleGraph_adj.2 ⟨edgeVertex_ne_double e e.2,
    Or.inl (mem_dominationGraph_snd.2 (Or.inr (Or.inr ⟨e, he, rfl, Or.inr rfl⟩)))⟩

/-- The only neighbour of the pendant `3` is the hub `1`. -/
private theorem eq_one_of_adj_three {G : Graph} {s : ℕ}
    (h : (dominationGraph G).toSimpleGraph.Adj 3 s) : s = 1 := by
  obtain ⟨-, h | h⟩ := Graph.toSimpleGraph_adj.1 h <;> rw [mem_dominationGraph_snd] at h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨e, -, h, -⟩
    exacts [absurd h (by decide), absurd h (by decide), absurd h.symm (edgeVertex_ne_three e)]
  · rcases h with ⟨h, -⟩ | ⟨-, v, -, h⟩ | ⟨e, -, -, h | h⟩
    exacts [h, absurd h.symm (double_ne_three v), absurd h.symm (double_ne_three e.1),
      absurd h.symm (double_ne_three e.2)]

/-- The only neighbours of the vertex of an edge are the copies of its endpoints. -/
private theorem of_adj_edgeVertex {G : Graph} {e : ℕ × ℕ} {s : ℕ}
    (h : (dominationGraph G).toSimpleGraph.Adj (edgeVertex e) s) : s = 2 * e.1 ∨ s = 2 * e.2 := by
  obtain ⟨-, h | h⟩ := Graph.toSimpleGraph_adj.1 h <;> rw [mem_dominationGraph_snd] at h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨e', -, h, hs⟩
    exacts [absurd h (edgeVertex_ne_one e), absurd h (edgeVertex_ne_one e),
      edgeVertex_injective h ▸ hs]
  · rcases h with ⟨-, h⟩ | ⟨-, v, -, h⟩ | ⟨e', -, -, h | h⟩
    exacts [absurd h (edgeVertex_ne_three e), absurd h (edgeVertex_ne_double e v),
      absurd h (edgeVertex_ne_double e e'.1), absurd h (edgeVertex_ne_double e e'.2)]

/-- Read a vertex of `dominationGraph G` back in `G`: the copy `2v` gives `v`, and the vertex of an
edge `e` gives `e.1`. -/
private def decodeVertex (w : ℕ) : ℕ :=
  match vertexCodec.decode? w with
  | some (.inl v) => v
  | some (.inr (.inr e)) => e.1
  | _ => 0

private theorem decodeVertex_double (v : ℕ) : decodeVertex (2 * v) = v :=
  show decodeVertex (vertexCodec (.inl v)) = v by simp [decodeVertex]

private theorem decodeVertex_edgeVertex (e : ℕ × ℕ) : decodeVertex (edgeVertex e) = e.1 := by
  simp [decodeVertex, edgeVertex]

/-- The reduction from `VertexCover` to `DominatingSet`: the graph `dominationGraph G` with the
target `k + 1`, or the unsatisfiable target `0` when `k` exceeds the number of distinct declared
vertices. -/
@[expose]
def toDominatingSet : VertexCoverInstance → DominatingSetInstance := fun x =>
  ⟨dominationGraph x.graph, if x.k ≤ x.graph.vertices.toFinset.card then x.k + 1 else 0⟩

/-- A vertex cover of `k` vertices, with the hub, dominates `dominationGraph G`. -/
private theorem mem_DominatingSet_of_mem_VertexCover {G : Graph} {k : ℕ}
    (h : (⟨G, k⟩ : VertexCoverInstance) ∈ VertexCover) :
    (⟨dominationGraph G, k + 1⟩ : DominatingSetInstance) ∈ DominatingSet := by
  classical
  obtain ⟨C, hCV, hC, rfl⟩ := mem_VertexCover_iff_mk.1 h
  refine mem_DominatingSet_iff.2 ⟨insert 1 (C.image (2 * ·)), fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact mem_dominationGraph_fst.2 (Or.inl rfl)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
      exact mem_dominationGraph_fst.2 (Or.inr (Or.inr (Or.inl ⟨v, hCV v hv, rfl⟩)))
  · rcases mem_dominationGraph_fst.1 hw with rfl | rfl | ⟨v, hv, rfl⟩ | ⟨e, he, rfl⟩
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr ⟨1, Finset.mem_insert_self _ _, adj_three_one G⟩
    · exact Or.inr ⟨1, Finset.mem_insert_self _ _, adj_double_one hv⟩
    · obtain ⟨he2, he1V, he2V, hne⟩ := mem_properEdges.1 he
      rcases hC e.1 he1V e.2 he2V (Graph.toSimpleGraph_adj.2 ⟨hne, Or.inl he2⟩) with h1 | h2
      · exact Or.inr ⟨2 * e.1, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ h1),
          adj_edgeVertex_fst he⟩
      · exact Or.inr ⟨2 * e.2, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ h2),
          adj_edgeVertex_snd he⟩
  · rw [Finset.card_insert_of_notMem (fun h1 => by
      obtain ⟨v, -, hv⟩ := Finset.mem_image.1 h1
      omega), Finset.card_image_of_injective _ fun a b (hab : 2 * a = 2 * b) => by omega]

/-- A dominating set of `dominationGraph G` of `k + 1` vertices yields a vertex cover of at most
`k` vertices: drop the hub and the pendant, and read the remaining vertices back in `G`. -/
private theorem exists_cover_of_mem_DominatingSet {G : Graph} {k : ℕ}
    (h : (⟨dominationGraph G, k + 1⟩ : DominatingSetInstance) ∈ DominatingSet) :
    ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card ≤ k := by
  classical
  obtain ⟨D, hDV, hD, hcard⟩ := mem_DominatingSet_iff.1 h
  set S := (((D.erase 1).erase 3).image decodeVertex).filter (· ∈ G.vertices)
  have hmem (w) (hw : w ∈ D) (h1 : w ≠ 1) (h3 : w ≠ 3) (hG : decodeVertex w ∈ G.vertices) :
      decodeVertex w ∈ S := Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _
    (Finset.mem_erase.2 ⟨h3, Finset.mem_erase.2 ⟨h1, hw⟩⟩), hG⟩
  -- A chosen copy `2v` of a declared vertex `v` puts `v` in the cover.
  have hdouble (v) (hv : v ∈ G.vertices) (hvD : 2 * v ∈ D) : v ∈ S := by
    simpa only [decodeVertex_double] using
      hmem _ hvD (by omega) (by omega) (by rwa [decodeVertex_double])
  -- The vertex of a proper edge is dominated by itself or by the copy of an endpoint.
  have hedge (e) (he : e ∈ properEdges G) : e.1 ∈ S ∨ e.2 ∈ S := by
    obtain ⟨-, he1, he2, -⟩ := mem_properEdges.1 he
    rcases hD _ (mem_dominationGraph_fst.2 (Or.inr (Or.inr (Or.inr ⟨e, he, rfl⟩)))) with
      hw | ⟨s, hs, hadj⟩
    · refine Or.inl ?_
      simpa only [decodeVertex_edgeVertex] using
        hmem _ hw (edgeVertex_ne_one e) (edgeVertex_ne_three e) (by rwa [decodeVertex_edgeVertex])
    · rcases of_adj_edgeVertex hadj with rfl | rfl
      exacts [Or.inl (hdouble e.1 he1 hs), Or.inr (hdouble e.2 he2 hs)]
  refine ⟨S, fun v hv => (Finset.mem_filter.1 hv).2, fun u hu v hv huv => ?_, ?_⟩
  · obtain ⟨hne, he | he⟩ := Graph.toSimpleGraph_adj.1 huv
    exacts [hedge _ (mem_properEdges.2 ⟨he, hu, hv, hne⟩),
      (hedge _ (mem_properEdges.2 ⟨he, hv, hu, hne.symm⟩)).symm]
  · -- The pendant `3` is dominated by itself or by the hub, so `D` loses a vertex.
    have hD' : ((D.erase 1).erase 3).card + 1 ≤ D.card := by
      rcases hD 3 (mem_dominationGraph_fst.2 (Or.inr (Or.inl rfl))) with h3D | ⟨s, hs, hadj⟩
      · have := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨(by decide : (3 : ℕ) ≠ 1), h3D⟩)
        have := Finset.card_erase_le (s := D) (a := 1)
        omega
      · obtain rfl := eq_one_of_adj_three hadj
        have := Finset.card_erase_add_one hs
        have := Finset.card_erase_le (s := D.erase 1) (a := 3)
        omega
    exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by omega))

/-- **Vertex covers of `G` are dominating sets of `dominationGraph G` with the hub.** -/
theorem toDominatingSet_mem_iff (x : VertexCoverInstance) :
    toDominatingSet x ∈ DominatingSet ↔ x ∈ VertexCover := by
  obtain ⟨G, k⟩ := x
  simp only [toDominatingSet]
  split_ifs with hk
  · refine ⟨fun h => ?_, mem_DominatingSet_of_mem_VertexCover⟩
    obtain ⟨S, hSV, hS, hcard⟩ := exists_cover_of_mem_DominatingSet h
    exact mem_VertexCover_iff_exists_card_le_mk.2 ⟨hk, S, hSV, hS, hcard⟩
  · refine ⟨fun h => ?_, fun h => absurd (mem_VertexCover_iff_exists_card_le_mk.1 h).1 hk⟩
    -- No dominating set of `0` vertices dominates the hub.
    obtain ⟨D, -, hD, hcard⟩ := mem_DominatingSet_iff.1 h
    obtain rfl := Finset.card_eq_zero.1 hcard
    have := hD 1 (mem_dominationGraph_fst.2 (Or.inl rfl))
    simp at this

/-- The vertex of an edge is computable in polynomial time from the binary endpoints. -/
@[fun_prop]
theorem computableInPolyTime_edgeVertex :
    ComputableInPolyTime edgeVertex (encPair encNat encNat) encNat := by
  unfold edgeVertex
  simp only [vertexCodec, NatCodec.sum_inr, NatCodec.finSum_inr]
  fun_prop

/-- The graph of the reduction is computable in polynomial time. The four lists are certified
separately: `fun_prop` alone times out on the whole graph. -/
@[fun_prop]
theorem computableInPolyTime_dominationGraph :
    ComputableInPolyTime dominationGraph encGraph encGraph := by
  have hfst : ComputableInPolyTime (fun G : Graph => G.vertices) encGraph (encList encNat) := by
    fun_prop
  have hV : ComputableInPolyTime (fun G : Graph => 1 :: 3 :: G.vertices.map (2 * ·)) encGraph
      (encList encNat) :=
    (show ComputableInPolyTime (fun V : List ℕ => 1 :: 3 :: V.map (2 * ·)) (encList encNat)
      (encList encNat) by fun_prop).comp hfst
  have hW : ComputableInPolyTime (fun G : Graph => (properEdges G).map edgeVertex) encGraph
      (encList encNat) :=
    (show ComputableInPolyTime (fun E : List (ℕ × ℕ) => E.map edgeVertex)
      (encList (encPair encNat encNat)) (encList encNat) by fun_prop).comp
      computableInPolyTime_properEdges
  have hEV : ComputableInPolyTime (fun G : Graph => (1, 3) :: G.vertices.map fun v => (1, 2 * v))
      encGraph (encList (encPair encNat encNat)) :=
    (show ComputableInPolyTime (fun V : List ℕ => (1, 3) :: V.map fun v => (1, 2 * v))
      (encList encNat) (encList (encPair encNat encNat)) by fun_prop).comp hfst
  have hEW : ComputableInPolyTime (fun G : Graph => (properEdges G).flatMap
      fun e => [(edgeVertex e, 2 * e.1), (edgeVertex e, 2 * e.2)])
      encGraph (encList (encPair encNat encNat)) :=
    (show ComputableInPolyTime (fun E : List (ℕ × ℕ) =>
      E.flatMap fun e => [(edgeVertex e, 2 * e.1), (edgeVertex e, 2 * e.2)])
      (encList (encPair encNat encNat)) (encList (encPair encNat encNat)) by fun_prop).comp
      computableInPolyTime_properEdges
  unfold dominationGraph
  exact encGraph_mk_polyTime
    (listAppend' hV hW)
    (listAppend' hEV hEW)

/-- The reduction `toDominatingSet` is polynomial-time: the binary target is compared with the
number of distinct declared vertices, computed in unary. -/
@[fun_prop]
theorem computableInPolyTime_toDominatingSet :
    ComputableInPolyTime toDominatingSet encVertexCoverInstance encDominatingSet := by
  have hle : ComputableInPolyTime
      (fun x : VertexCoverInstance => decide (x.k ≤ x.graph.vertices.toFinset.card))
      encVertexCoverInstance encBool := by
    simp_rw [← Graph.length_distinctVertices]
    fun_prop
  have heq : toDominatingSet = fun x : VertexCoverInstance =>
      ⟨dominationGraph x.graph,
        if decide (x.k ≤ x.graph.vertices.toFinset.card) then x.k + 1 else 0⟩ := by
    funext ⟨G, k⟩
    simp only [toDominatingSet, decide_eq_true_eq]
  rw [heq]
  exact encDominatingSet_mk_polyTime
    (computableInPolyTime_dominationGraph.comp (by fun_prop))
    (ite' hle (by fun_prop) (const 0))

end VertexCover

/-- `VertexCover` reduces to `DominatingSet` in polynomial time via
`VertexCover.toDominatingSet`. -/
theorem polyTimeReducible_VertexCover_DominatingSet :
    PolyTimeReducible encVertexCoverInstance encDominatingSet VertexCover
      DominatingSet :=
  ⟨VertexCover.toDominatingSet, VertexCover.computableInPolyTime_toDominatingSet,
    fun x => (VertexCover.toDominatingSet_mem_iff x).symm⟩

/-- `DominatingSet` is `NP`-hard. -/
theorem DominatingSet_npHard : NPHard encDominatingSet DominatingSet :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_DominatingSet

/-- **`DominatingSet` is NP-complete** [Garey and Johnson, Problem GT2][GareyJohnson1979], with the
target in binary. -/
theorem DominatingSet_npComplete : NPComplete encDominatingSet DominatingSet :=
  ⟨DominatingSet.mem_NP, DominatingSet_npHard⟩

end Cslib.Complexity
