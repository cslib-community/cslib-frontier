/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.BoundedSTCON
public import CslibFrontier.Computability.Complexity.Problems.USTCON
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.RelatesInSteps

/-!
# Distances in undirected graphs

A `UDistanceInstance` is an instance of undirected `s`–`t` connectivity (`USTCONInstance`, a
symmetric loopless adjacency matrix with two terminals) together with a natural number `K`. Exercise
5.24 of Goldreich's January 2007 draft ("determining distances in undirected graphs", printed
p. 198) asks whether there is a path of length at most `K` from `s` to `t`
(`Cslib.Complexity.UDistanceAtMost`), respectively exactly `K` (`Cslib.Complexity.UDistanceEq`).
**The second set is an interpretation, not the literal question.** Read literally, "a path of
length exactly `K`" asks for a simple path with `K` edges: on a triangle with adjacent terminals
there is one for `K = 2`, while the distance is `1`. The exercise's title, its guideline for the
exact version (which uses `NL = coNL`, needed only for a lower bound on the distance) and
Exercise 5.27 support the shortest-distance reading, which `UDistanceEq` formalizes: the distance
is exactly `K`. Both sets are stated with Mathlib's extended distance `SimpleGraph.edist`, which is
`⊤` between disconnected vertices, so disconnected pairs belong to neither. A walk of length at
most `K` shortens to a path of length at most `K`, so the first set is literally the source's.

Instances are encoded (`Cslib.Complexity.encUDistance`) as a framed `encUSTCON` word followed by
the binary digits of `K`; this is the layout of `Cslib.Complexity.encBoundedSTCON` on the directed
graph of the instance (`Cslib.Complexity.UDistanceInstance.encBoundedSTCON_toBoundedSTCON`).

This module proves the graph-theoretic facts behind the logarithmic-space reductions:

* **At most `K`** is bounded directed connectivity on the directed graph of the instance
  (`Cslib.Complexity.UDistanceInstance.toBoundedSTCON_mem_iff`).
* **Less than `K`**: appending a new vertex after `t`, joined to `t` by one arc
  (`Cslib.Complexity.STCONInstance.pendant`), turns "within `K - 1` arcs to `t`" into "within `K`
  arcs to the new vertex" for every `K`, including `K = 0`
  (`Cslib.Complexity.UDistanceInstance.strict_mem_iff`). The distance is `K` exactly when it is at
  most `K` and not less than `K` (`Cslib.Complexity.UDistanceInstance.mem_UDistanceEq_iff`).
* **Hardness**: the guideline's layered graph of a directed instance `J` on `n` vertices is the
  undirected graph (`Cslib.Complexity.STCONInstance.undirected`) of the directed layered graph
  `Cslib.Complexity.BoundedSTCONInstance.layered` with `n + 1` layers. Every walk from `(0, s)` to
  `(n, t)` has at least `n` edges, and one with `n` edges climbs one layer per edge, following an
  arc of `J` or staying at its vertex. So `t` is reachable from `s` exactly when the distance is at
  most `n`, and exactly when it is `n`
  (`Cslib.Complexity.STCONInstance.distanceInstance_mem_UDistanceAtMost_iff`,
  `Cslib.Complexity.STCONInstance.distanceInstance_mem_UDistanceEq_iff`). The guideline uses
  `|V|` layers and the bound `|V| - 1`; one more layer avoids the case `n = 0` in the subtraction
  and changes nothing else.

## Main definitions

* `Cslib.Complexity.UDistanceInstance`, `Cslib.Complexity.encUDistance`: instances and their
  encoding.
* `Cslib.Complexity.UDistanceAtMost`, `Cslib.Complexity.UDistanceEq`: distance at most `K`, and
  exactly `K`.
* `Cslib.Complexity.STCONInstance.pendant`: a new target after `t`.
* `Cslib.Complexity.STCONInstance.undirected`: the undirected graph of a directed instance.
* `Cslib.Complexity.STCONInstance.distanceInstance`: the layered hardness instance.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, January 2007 draft,
  Exercise 5.24][Goldreich2007DraftR2]
-/

public section

namespace Cslib.Complexity

/-- An instance of **distance in an undirected graph**: an undirected connectivity instance and a
natural number bound `K`. -/
structure UDistanceInstance where
  /-- The undirected graph, with its source and target. -/
  graph : USTCONInstance
  /-- The distance bound `K`, encoded in binary. -/
  bound : ℕ

open Turing.MultiTapeTM in
/-- A framed `encUSTCON` graph followed by the binary digits (`encNat`) of the bound. -/
enc_structure encUDistance : UDistanceInstance where
  graph : encUSTCON,
  bound : encNat

/-- **Distance at most `K`**: the instances with a path of at most `bound` edges from `s` to `t`
(Goldreich's January 2007 draft, Exercise 5.24, "at most"). -/
@[expose] def UDistanceAtMost : Set UDistanceInstance :=
  {I | I.graph.graph.edist I.graph.s I.graph.t ≤ I.bound}

/-- **Distance exactly `K`**: the instances whose terminals are at distance `bound`. This is the
shortest-distance reading of Goldreich's January 2007 draft, Exercise 5.24, "exactly", not the
literal "a path of exactly `bound` edges" (see the module docstring). -/
@[expose] def UDistanceEq : Set UDistanceInstance :=
  {I | I.graph.graph.edist I.graph.s I.graph.t = I.bound}

namespace STCONInstance

variable (I : STCONInstance)

/-- **A pendant target**: the instance with one more vertex `n`, the arcs of `I`, one arc from
`t` to `n`, and target `n`. -/
@[expose] def pendant : STCONInstance where
  n := I.n + 1
  adj a b :=
    if h : a.val < I.n ∧ b.val < I.n then I.adj ⟨a, h.1⟩ ⟨b, h.2⟩
    else decide (a.val = I.t ∧ b.val = I.n)
  s := I.s.castSucc
  t := Fin.last I.n

/-- Between old vertices, the pendant instance has the arcs of `I`. -/
theorem pendant_adj_castSucc (a b : Fin I.n) :
    I.pendant.Adj a.castSucc b.castSucc ↔ I.Adj a b := by
  simp [pendant, STCONInstance.Adj]

/-- The only arc into the new vertex comes from `t`. -/
theorem pendant_adj_last (a : Fin (I.n + 1)) :
    I.pendant.Adj a (Fin.last I.n) ↔ a = I.t.castSucc := by
  simp [pendant, STCONInstance.Adj, Fin.ext_iff]

/-- No arc leaves the new vertex. -/
theorem not_pendant_adj_last (b : Fin (I.n + 1)) : ¬I.pendant.Adj (Fin.last I.n) b := by
  have := I.t.isLt
  simp [pendant, STCONInstance.Adj]
  omega

/-- A chain of the pendant instance between old vertices is a chain of `I`. -/
private theorem relatesInSteps_of_pendant {a : Fin I.n} {k : ℕ} :
    ∀ {x : Fin (I.n + 1)}, Relation.RelatesInSteps I.pendant.Adj a.castSucc x k →
      ∀ b : Fin I.n, x = b.castSucc → Relation.RelatesInSteps I.Adj a b k := by
  intro x h b hb
  induction h generalizing b with
  | refl => exact Fin.castSucc_inj.mp hb ▸ .refl _
  | tail y _ _ _ hyz ih =>
    subst hb
    cases y using Fin.lastCases with
    | last => exact absurd hyz (I.not_pendant_adj_last _)
    | cast y => exact .tail _ _ _ _ (ih y rfl) ((I.pendant_adj_castSucc y b).mp hyz)

/-- A chain of `I` is a chain of the pendant instance. -/
private theorem relatesInSteps_pendant {a b : Fin I.n} {k : ℕ}
    (h : Relation.RelatesInSteps I.Adj a b k) :
    Relation.RelatesInSteps I.pendant.Adj a.castSucc b.castSucc k :=
  h.map _ fun y z hyz => (I.pendant_adj_castSucc y z).mpr hyz

/-- **The pendant target is reached within `k` arcs** exactly when `t` is reached within `k - 1`
arcs, for `k ≥ 1`; it is never reached within `0` arcs. -/
theorem relatesWithinSteps_pendant_iff (k : ℕ) :
    Relation.RelatesWithinSteps I.pendant.Adj I.pendant.s I.pendant.t k ↔
      ∃ j, j + 1 = k ∧ Relation.RelatesWithinSteps I.Adj I.s I.t j := by
  refine ⟨?_, fun ⟨_, hj, m, hm, h⟩ => ⟨m + 1, by omega,
    .tail _ _ _ _ (I.relatesInSteps_pendant h) ((I.pendant_adj_last _).mpr rfl)⟩⟩
  rintro ⟨_ | m, hm, h⟩
  · exact absurd (congrArg Fin.val h.zero) (by simp [pendant]; omega)
  · obtain ⟨y, hy, hyl⟩ := h.succ
    exact ⟨k - 1, by omega, m, by omega,
      I.relatesInSteps_of_pendant hy _ ((I.pendant_adj_last y).mp hyl)⟩

/-- **The undirected graph of a directed instance**: distinct vertices are adjacent when there is
an arc between them in either direction. The terminals are kept. -/
@[expose] def undirected : USTCONInstance where
  n := I.n
  adj a b := decide (a ≠ b) && (I.adj a b || I.adj b a)
  symm a b := by cases I.adj a b <;> cases I.adj b a <;> simp [ne_comm]
  loopless a := by simp
  s := I.s
  t := I.t

/-- The entries of the undirected graph of a directed instance. -/
theorem undirected_adj (a b : Fin I.n) :
    I.undirected.adj a b = (decide (a ≠ b) && (I.adj a b || I.adj b a)) :=
  rfl

/-- Adjacency in the undirected graph of a directed instance. -/
theorem undirected_adj_iff (a b : Fin I.n) :
    I.undirected.graph.Adj a b ↔ a ≠ b ∧ (I.Adj a b ∨ I.Adj b a) := by
  simp [undirected, STCONInstance.Adj]

/-- **The layered hardness instance** of Exercise 5.24: the undirected graph of the directed
layered graph with `n + 1` layers (`BoundedSTCONInstance.layered` for the bound `n`), from
`(0, s)` to `(n, t)`, with distance bound `n`. -/
@[expose] def distanceInstance : UDistanceInstance :=
  ⟨(⟨I, I.n⟩ : BoundedSTCONInstance).layered.undirected, I.n⟩

end STCONInstance

namespace UDistanceInstance

variable (I : UDistanceInstance)

/-- The bounded directed connectivity instance on the directed graph of the instance. -/
@[expose] def toBoundedSTCON : BoundedSTCONInstance := ⟨I.graph.toSTCONInstance, I.bound⟩

/-- The bounded directed instance asking for the pendant target after `t` within the bound. -/
@[expose] def strict : BoundedSTCONInstance := ⟨I.graph.toSTCONInstance.pendant, I.bound⟩

/-- The encoding of an instance is that of its bounded directed instance. -/
theorem encBoundedSTCON_toBoundedSTCON : encBoundedSTCON I.toBoundedSTCON = encUDistance I :=
  rfl

/-- The encoding of an instance as a pair. -/
theorem encUDistance_eq_encPair :
    encUDistance I = Turing.MultiTapeTM.encPair encSTCON Turing.MultiTapeTM.encNat
      (I.graph.toSTCONInstance, I.bound) :=
  rfl

/-- The distance is at most `K` exactly when the directed graph has a walk of at most `K` arcs. -/
private theorem edist_le_iff (k : ℕ) :
    I.graph.graph.edist I.graph.s I.graph.t ≤ k ↔
      Relation.RelatesWithinSteps I.graph.toSTCONInstance.Adj I.graph.s I.graph.t k :=
  SimpleGraph.edist_le_iff_relatesWithinSteps

/-- **Distance at most `K` is bounded directed connectivity** on the directed graph. -/
theorem toBoundedSTCON_mem_iff : I.toBoundedSTCON ∈ BoundedSTCON ↔ I ∈ UDistanceAtMost :=
  (I.edist_le_iff I.bound).symm

/-- **Distance less than `K`**: the pendant target is reached within `K` arcs exactly when the
distance is less than `K`. -/
theorem strict_mem_iff :
    I.strict ∈ BoundedSTCON ↔ I.graph.graph.edist I.graph.s I.graph.t < I.bound := by
  change Relation.RelatesWithinSteps I.graph.toSTCONInstance.pendant.Adj
    I.graph.toSTCONInstance.pendant.s I.graph.toSTCONInstance.pendant.t I.bound ↔ _
  rw [STCONInstance.relatesWithinSteps_pendant_iff]
  refine ⟨fun ⟨j, hj, h⟩ =>
    ((I.edist_le_iff j).mpr h).trans_lt (by exact_mod_cast (by omega : j < I.bound)), fun h => ?_⟩
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp h.ne_top
  have : d < I.bound := by exact_mod_cast hd ▸ h
  exact ⟨I.bound - 1, by omega, (I.edist_le_iff _).mp (by rw [← hd]; exact_mod_cast (by omega))⟩

/-- **The distance is `K`** exactly when it is at most `K` and the pendant target is not reached
within `K` arcs. -/
theorem mem_UDistanceEq_iff :
    I ∈ UDistanceEq ↔ I.toBoundedSTCON ∈ BoundedSTCON ∧ I.strict ∉ BoundedSTCON := by
  rw [toBoundedSTCON_mem_iff, strict_mem_iff]
  exact ⟨fun h => ⟨h.le, h.not_lt⟩, fun h => le_antisymm h.1 (not_lt.mp h.2)⟩

end UDistanceInstance

/-! ### The layered hardness instance -/

namespace STCONInstance

variable (J : STCONInstance)

private abbrev B : BoundedSTCONInstance := ⟨J, J.n⟩

private theorem cap_B : (B J).cap = J.n := min_self _

/-- The layer of a vertex of the layered graph. -/
private def layer (x : Fin (B J).layered.n) : ℕ := (finProdFinEquiv.symm x).1.val

/-- The original vertex of a vertex of the layered graph. -/
private def vertex (x : Fin (B J).layered.n) : Fin J.n := (finProdFinEquiv.symm x).2

private theorem node_layer_vertex (x : Fin (B J).layered.n) :
    (B J).node (finProdFinEquiv.symm x).1 (vertex J x) = x :=
  Equiv.apply_symm_apply _ x

private theorem layer_node (i : Fin ((B J).cap + 1)) (v : Fin J.n) :
    layer J ((B J).node i v) = i := by
  simp [layer, BoundedSTCONInstance.node]

private theorem vertex_node (i : Fin ((B J).cap + 1)) (v : Fin J.n) :
    vertex J ((B J).node i v) = v := by
  simp [vertex, BoundedSTCONInstance.node]

/-- An arc of the layered graph climbs one layer and follows an arc of `J` or stays. -/
private theorem layered_adj {x y : Fin (B J).layered.n} (h : (B J).layered.Adj x y) :
    layer J y = layer J x + 1 ∧ Relation.ReflGen J.Adj (vertex J x) (vertex J y) := by
  rwa [← node_layer_vertex J x, ← node_layer_vertex J y, BoundedSTCONInstance.layered_adj_iff] at h

/-- **Walks of the layered undirected graph climb at most one layer per edge**, and a walk that
climbs one layer per edge is a chain of arcs of `J` or stays. -/
private theorem walk_layer {x y : Fin (B J).layered.undirected.n}
    (p : (B J).layered.undirected.graph.Walk x y) :
    layer J y ≤ layer J x + p.length ∧
      (layer J y = layer J x + p.length →
        Relation.RelatesInSteps (Relation.ReflGen J.Adj) (vertex J x) (vertex J y) p.length) := by
  induction p with
  | nil => exact ⟨by simp, fun _ => .refl _⟩
  | @cons x z y h q ih =>
    rw [SimpleGraph.Walk.length_cons]
    rcases (((B J).layered.undirected_adj_iff x z).mp h).2 with h | h <;>
      obtain ⟨hl, hr⟩ := layered_adj J h
    · exact ⟨by omega, fun _ => .head _ _ _ _ hr (ih.2 (by omega))⟩
    · exact ⟨by omega, fun _ => by omega⟩

/-- A chain of arcs of `J` or stays climbs the layers of the layered undirected graph. -/
private theorem walk_of_relatesInSteps {v : Fin J.n} {k : ℕ}
    (h : Relation.RelatesInSteps (Relation.ReflGen J.Adj) J.s v k) (hk : k ≤ (B J).cap) :
    ∃ p : (B J).layered.undirected.graph.Walk ((B J).node ⟨0, by omega⟩ J.s)
      ((B J).node ⟨k, by omega⟩ v), p.length = k := by
  induction h with
  | refl => exact ⟨.nil, rfl⟩
  | tail u w k _ huw ih =>
    obtain ⟨p, hp⟩ := ih (by omega)
    have hadj : (B J).layered.undirected.graph.Adj ((B J).node ⟨k, by omega⟩ u)
        ((B J).node ⟨k + 1, by omega⟩ w) :=
      ((B J).layered.undirected_adj_iff _ _).mpr ⟨fun he => by
        simpa [layer_node] using congrArg (layer J) he,
        .inl (((B J).layered_adj_iff _ _ _ _).mpr ⟨rfl, huw⟩)⟩
    exact ⟨p.concat hadj, (p.length_concat hadj).trans (by rw [hp])⟩

/-- Every walk of the hardness instance has at least `n` edges. -/
private theorem le_edist_distanceInstance :
    (J.n : ℕ∞) ≤ J.distanceInstance.graph.graph.edist J.distanceInstance.graph.s
      J.distanceInstance.graph.t := by
  rcases eq_or_ne (J.distanceInstance.graph.graph.edist J.distanceInstance.graph.s
    J.distanceInstance.graph.t) ⊤ with htop | htop
  · exact htop ▸ le_top
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
  have h : layer J ((B J).node _ _) ≤ layer J ((B J).node _ _) + p.length := (walk_layer J p).1
  simp only [layer_node, cap_B] at h
  exact hp ▸ mod_cast (by omega : J.n ≤ p.length)

/-- **Reachability gives a walk of `n` edges** in the hardness instance. -/
private theorem edist_distanceInstance_le (h : J ∈ STCON) :
    J.distanceInstance.graph.graph.edist J.distanceInstance.graph.s
      J.distanceInstance.graph.t ≤ J.n := by
  obtain ⟨p, hp⟩ := walk_of_relatesInSteps J
    (Relation.relatesWithinSteps_iff_relatesInSteps_reflGen.mp
      ((B J).capped_iff.mpr ((Relation.reflTransGen_iff_relatesWithinSteps (by simp)).mp h))) le_rfl
  exact (SimpleGraph.edist_le p).trans (by rw [hp, cap_B])

/-- A walk of at most `n` edges in the hardness instance gives reachability. -/
private theorem mem_of_edist_distanceInstance_le
    (h : J.distanceInstance.graph.graph.edist J.distanceInstance.graph.s
      J.distanceInstance.graph.t ≤ J.n) : J ∈ STCON := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h)
  have hlen : p.length ≤ J.n := by exact_mod_cast hp ▸ h
  obtain ⟨hle, heq⟩ := walk_layer J p
  change layer J ((B J).node _ _) ≤ layer J ((B J).node _ _) + p.length at hle
  change layer J ((B J).node _ _) = layer J ((B J).node _ _) + p.length →
    Relation.RelatesInSteps _ (vertex J ((B J).node _ _)) (vertex J ((B J).node _ _)) _ at heq
  simp only [layer_node, vertex_node, cap_B] at hle heq
  rw [mem_STCON, ← Relation.reflTransGen_reflGen]
  exact (heq (by omega)).reflTransGen

/-- **Hardness, "at most"**: `t` is reachable from `s` exactly when the hardness instance has
distance at most `n`. -/
theorem distanceInstance_mem_UDistanceAtMost_iff :
    J.distanceInstance ∈ UDistanceAtMost ↔ J ∈ STCON :=
  ⟨J.mem_of_edist_distanceInstance_le, J.edist_distanceInstance_le⟩

/-- **Hardness, "exactly"**: `t` is reachable from `s` exactly when the hardness instance has
distance exactly `n`. -/
theorem distanceInstance_mem_UDistanceEq_iff :
    J.distanceInstance ∈ UDistanceEq ↔ J ∈ STCON :=
  ⟨fun h => J.mem_of_edist_distanceInstance_le h.le,
    fun h => le_antisymm (J.edist_distanceInstance_le h) J.le_edist_distanceInstance⟩

end STCONInstance

end Cslib.Complexity
