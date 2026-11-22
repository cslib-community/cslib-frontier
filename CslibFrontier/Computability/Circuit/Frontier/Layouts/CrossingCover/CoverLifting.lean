/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Submodular
public import Mathlib.Combinatorics.SimpleGraph.Finite
import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite graph covers, crossing-cover lifting, and high-girth covers

A finite `m`-sheeted covering map `cov : SimpleGraphCover H' H m` from a simple graph `H'` on
`V'` to a simple graph `H` on `V` is a projection `proj : V' → V` whose fibers all have cardinality
`m > 0`, which maps edges to edges, and which lifts every incident edge uniquely at each vertex of
the fiber.

We prove two core graph-covering theorems and a local-tree corollary:

1. **Exact crossing-cover lifting (`simpleCrossingCover_lift_eq`):** For every finite covering map
   `cov : SimpleGraphCover H' H m` and vertex bipartition `b : V → Bool`, the minimum crossing
   vertex cover lifts with exact scaling:
   `simpleCrossingCover H' (b ∘ cov.proj) = m * simpleCrossingCover H b`.
   The upper bound pulls back a minimum crossing cover of `H` along `cov.proj`. The lower bound
   applies König's theorem (`Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`)
   to the crossing bipartite graph of `(H, b)` to obtain a crossing matching `M` of cardinality
   `simpleCrossingCover H b`; each edge of `M` lifts to a perfect matching of size `m` between
   disjoint fibers in `H'`, forcing every crossing cover of `H'` to contain at least `m` vertices
   across each matched pair of fibers.

2. **Finite covers of arbitrarily large girth (`exists_cover_girth_gt`):** For every finite simple
   graph `H` and integer `g : ℕ`, there exist a finite group `Q` and a voltage covering graph `H'`
   on `V × Q` (`m = Fintype.card Q > 0`) that has no closed non-backtracking walk of length
   `1 ≤ j ≤ g`. Indeed, assigning generators to all undirected edges of `H` inside the finite
   product group of symmetric groups extending the partial shift permutations associated with each
   reduced edge-word of length `1 ≤ k ≤ g` guarantees that *every* non-backtracking walk of length
   `1 ≤ j ≤ g` yields a non-identity group element in `Q`. Taking a single connected component
   (`SimpleGraphCover.restrictComponent`) gives a connected high-girth cover whenever `H` is
   connected (`exists_connected_cover_girth_gt`).

3. **Uniqueness of short non-backtracking walks (`lift_nbWalk_injective_ball`):** In any simple
   graph with no closed non-backtracking walk of length `1 ≤ j ≤ 2 * r`, two non-backtracking
   walks of lengths at most `r` sharing both endpoints must coincide.

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.SimpleGraphCover`: finite `m`-sheeted covering map of
  simple graphs, with `fiber`, `liftNeighbor`, `fiberEquiv`, `neighborEquiv`, `liftWalk`, and
  `restrictComponent`.
* `Cslib.Circuits.Frontier.CrossingCover.ofSimpleGraph`: canonical `Multigraph` of a `SimpleGraph`.
* `Cslib.Circuits.Frontier.CrossingCover.IsSimpleCrossingCover`,
  `Cslib.Circuits.Frontier.CrossingCover.simpleCrossingCover`: crossing vertex cover of a simple
  graph, matching `crossingCover` on the associated multigraph.
* `Cslib.Circuits.Frontier.CrossingCover.IsNBWalk`: non-backtracking walk of fixed length.
* `Cslib.Circuits.Frontier.CrossingCover.voltageGraph`,
  `Cslib.Circuits.Frontier.CrossingCover.voltageCover`: group-valued voltage covering graph.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.simpleCrossingCover_toSimpleGraph`: exact equality
  `simpleCrossingCover G.toSimpleGraph b = crossingCover G b` for every multigraph `G`.
* `Cslib.Circuits.Frontier.CrossingCover.exists_crossingMatching_eq_simpleCrossingCover`:
  König's theorem specialized to the crossing edges of `(H, b)`.
* `Cslib.Circuits.Frontier.CrossingCover.simpleCrossingCover_lift_eq`:
  `simpleCrossingCover H' (b ∘ cov.proj) = m * simpleCrossingCover H b`.
* `Cslib.Circuits.Frontier.CrossingCover.crossingCover_lift_eq`: multigraph version of lifting.
* `Cslib.Circuits.Frontier.CrossingCover.exists_cover_girth_gt`: finite voltage cover on `V × Q`
  with no closed non-backtracking walk of length `1 ≤ j ≤ g`.
* `Cslib.Circuits.Frontier.CrossingCover.exists_connected_cover_girth_gt`: connected variant for a
  connected base graph `H`.
* `Cslib.Circuits.Frontier.CrossingCover.lift_nbWalk_injective_ball`: uniqueness of lifted
  non-backtracking walks of length at most `r` in a cover of girth `> 2 * r + 1`.
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset Function

/-! ### Finite `m`-sheeted simple graph covers -/

/-- A finite `m`-sheeted covering map from a simple graph `H'` to a simple graph `H`. Each base
vertex has a fiber of cardinality `m > 0`, adjacent vertices project to adjacent vertices, and
every base edge incident to `proj u'` lifts uniquely to an edge incident to `u'`. -/
structure SimpleGraphCover {V' V : Type*} (H' : SimpleGraph V') (H : SimpleGraph V) (m : ℕ) where
  /-- The covering projection sending each vertex of `H'` to its base vertex in `H`. -/
  proj : V' → V
  /-- Every sheet count is positive. -/
  hm : 0 < m
  /-- Every fiber `proj⁻¹(v)` has exact cardinality `m`. -/
  card_fiber_set : ∀ v : V, {v' : V' | proj v' = v}.ncard = m
  /-- The projection preserves adjacency. -/
  adj_proj : ∀ {u' v' : V'}, H'.Adj u' v' → H.Adj (proj u') (proj v')
  /-- Unique edge lifting at each vertex of `H'`. -/
  lift_adj : ∀ (u' : V') (v : V), H.Adj (proj u') v → ∃! v' : V', proj v' = v ∧ H'.Adj u' v'

namespace SimpleGraphCover

section Basic

variable {V' V : Type*} {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}

/-- Build a `SimpleGraphCover` using `Finset.card` of filtered fibers on a finite vertex type. -/
@[expose] def ofFinsetCard [Fintype V'] [DecidableEq V]
    (proj : V' → V) (hm : 0 < m)
    (card_fiber : ∀ v : V, (Finset.univ.filter fun v' => proj v' = v).card = m)
    (adj_proj : ∀ {u' v' : V'}, H'.Adj u' v' → H.Adj (proj u') (proj v'))
    (lift_adj : ∀ (u' : V') (v : V), H.Adj (proj u') v →
      ∃! v' : V', proj v' = v ∧ H'.Adj u' v') :
    SimpleGraphCover H' H m where
  proj := proj
  hm := hm
  card_fiber_set v := by
    have hset : ({v' : V' | proj v' = v} : Set V') =
        ↑(Finset.univ.filter fun v' : V' => proj v' = v) := by
      ext v'; simp
    rw [hset, Set.ncard_coe_finset]
    exact card_fiber v
  adj_proj := adj_proj
  lift_adj := lift_adj

variable (cov : SimpleGraphCover H' H m)

/-- The fiber of `v : V` as a `Finset V'`. -/
@[expose] def fiber [Fintype V'] [DecidableEq V] (v : V) : Finset V' :=
  Finset.univ.filter fun v' => cov.proj v' = v

@[simp] theorem mem_fiber [Fintype V'] [DecidableEq V] {v : V} {v' : V'} :
    v' ∈ cov.fiber v ↔ cov.proj v' = v := by
  simp [fiber]

theorem card_fiber [Fintype V'] [DecidableEq V] (v : V) :
    (cov.fiber v).card = m := by
  have hset : ({v' : V' | cov.proj v' = v} : Set V') = ↑(cov.fiber v) := by
    ext v'; simp [fiber]
  rw [← Set.ncard_coe_finset, ← hset]
  exact cov.card_fiber_set v

theorem card_subtype_fiber (v : V) [Fintype {v' : V' // cov.proj v' = v}] :
    Fintype.card {v' : V' // cov.proj v' = v} = m := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_coe_set_eq {v' : V' | cov.proj v' = v}).trans (cov.card_fiber_set v)

theorem disjoint_fiber [Fintype V'] [DecidableEq V] {u v : V} (h : u ≠ v) :
    Disjoint (cov.fiber u) (cov.fiber v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  exact h ((mem_fiber cov).mp hxu ▸ (mem_fiber cov).mp hxv)

include cov in
theorem card_vert_eq [Fintype V'] [Fintype V] :
    Fintype.card V' = m * Fintype.card V := by
  classical
  calc Fintype.card V'
      = (Finset.univ : Finset V').card := rfl
    _ = ∑ v : V, (Finset.univ.filter fun v' : V' => cov.proj v' = v).card :=
        Finset.card_eq_sum_card_fiberwise (fun v' _ => Finset.mem_univ (cov.proj v'))
    _ = ∑ _v : V, m := Finset.sum_congr rfl fun v _ => cov.card_fiber v
    _ = Fintype.card V * m := by simp
    _ = m * Fintype.card V := Nat.mul_comm _ _

include cov in
theorem natCard_vert_eq [Finite V'] [Finite V] :
    Nat.card V' = m * Nat.card V := by
  have := Fintype.ofFinite V'
  have := Fintype.ofFinite V
  simpa only [Nat.card_eq_fintype_card] using cov.card_vert_eq

theorem proj_surjective [Finite V'] : Function.Surjective cov.proj := by
  intro v
  have hne : ({v' : V' | cov.proj v' = v} : Set V').Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    rw [cov.card_fiber_set v]
    exact cov.hm
  exact hne

/-- The unique neighbor of `u'` projecting to `v` across a base edge `H.Adj (cov.proj u') v`. -/
noncomputable def liftNeighbor (u' : V') {v : V} (h : H.Adj (cov.proj u') v) : V' :=
  Classical.choose (cov.lift_adj u' v h).exists

theorem proj_liftNeighbor (u' : V') {v : V} (h : H.Adj (cov.proj u') v) :
    cov.proj (cov.liftNeighbor u' h) = v :=
  (Classical.choose_spec (cov.lift_adj u' v h).exists).1

theorem adj_liftNeighbor (u' : V') {v : V} (h : H.Adj (cov.proj u') v) :
    H'.Adj u' (cov.liftNeighbor u' h) :=
  (Classical.choose_spec (cov.lift_adj u' v h).exists).2

theorem eq_liftNeighbor {u' v' : V'} {v : V} (h : H.Adj (cov.proj u') v)
    (hp : cov.proj v' = v) (ha : H'.Adj u' v') :
    v' = cov.liftNeighbor u' h :=
  (cov.lift_adj u' v h).unique ⟨hp, ha⟩ (Classical.choose_spec (cov.lift_adj u' v h).exists)

theorem eq_of_adj_of_proj_eq {u' v₁' v₂' : V'}
    (h₁ : H'.Adj u' v₁') (h₂ : H'.Adj u' v₂') (hp : cov.proj v₁' = cov.proj v₂') :
    v₁' = v₂' :=
  (cov.lift_adj u' (cov.proj v₂') (cov.adj_proj h₂)).unique ⟨hp, h₁⟩ ⟨rfl, h₂⟩

/-- Every edge `H.Adj u v` lifts to a bijection (perfect matching) between the fibers over `u`
and `v`. -/
noncomputable def fiberEquiv {u v : V} (h : H.Adj u v) :
    {u' : V' // cov.proj u' = u} ≃ {v' : V' // cov.proj v' = v} where
  toFun u' := ⟨cov.liftNeighbor u'.1 (u'.2.symm ▸ h), cov.proj_liftNeighbor u'.1 _⟩
  invFun v' := ⟨cov.liftNeighbor v'.1 (v'.2.symm ▸ h.symm), cov.proj_liftNeighbor v'.1 _⟩
  left_inv u' := by
    apply Subtype.ext
    dsimp only
    let hu : H.Adj (cov.proj u'.1) v := u'.2.symm ▸ h
    let w' := cov.liftNeighbor u'.1 hu
    have hw : cov.proj w' = v := cov.proj_liftNeighbor u'.1 hu
    exact (cov.eq_liftNeighbor (hw.symm ▸ h.symm) u'.2 (cov.adj_liftNeighbor u'.1 hu).symm).symm
  right_inv v' := by
    apply Subtype.ext
    dsimp only
    let hv : H.Adj (cov.proj v'.1) u := v'.2.symm ▸ h.symm
    let w' := cov.liftNeighbor v'.1 hv
    have hw : cov.proj w' = u := cov.proj_liftNeighbor v'.1 hv
    exact (cov.eq_liftNeighbor (hw.symm ▸ h) v'.2 (cov.adj_liftNeighbor v'.1 hv).symm).symm

theorem fiberEquiv_adj {u v : V} (h : H.Adj u v) (u' : {u' : V' // cov.proj u' = u}) :
    H'.Adj u'.1 (cov.fiberEquiv h u').1 :=
  cov.adj_liftNeighbor u'.1 (u'.2.symm ▸ h)

theorem fiberEquiv_symm_adj {u v : V} (h : H.Adj u v) (v' : {v' : V' // cov.proj v' = v}) :
    H'.Adj ((cov.fiberEquiv h).symm v').1 v'.1 :=
  (cov.adj_liftNeighbor v'.1 (v'.2.symm ▸ h.symm)).symm

/-- Local isomorphism of neighborhoods: `cov.proj` restricts to a bijection between
`H'.neighborSet u'` and `H.neighborSet (cov.proj u')`. -/
noncomputable def neighborEquiv (u' : V') :
    H'.neighborSet u' ≃ H.neighborSet (cov.proj u') where
  toFun v' := ⟨cov.proj v'.1, cov.adj_proj v'.2⟩
  invFun v := ⟨cov.liftNeighbor u' v.2, cov.adj_liftNeighbor u' v.2⟩
  left_inv v' := Subtype.ext (cov.eq_liftNeighbor (cov.adj_proj v'.2) rfl v'.2).symm
  right_inv v := Subtype.ext (cov.proj_liftNeighbor u' v.2)

theorem ncard_neighborSet_eq (u' : V') :
    (H'.neighborSet u').ncard = (H.neighborSet (cov.proj u')).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (cov.neighborEquiv u')

theorem degree_eq (u' : V') [Fintype (H'.neighborSet u')]
    [Fintype (H.neighborSet (cov.proj u'))] :
    H'.degree u' = H.degree (cov.proj u') := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (cov.neighborEquiv u')

include cov in
theorem isRegularOfDegree {d : ℕ} [Fintype V'] [Fintype V]
    [DecidableRel H'.Adj] [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree d) : H'.IsRegularOfDegree d := by
  intro u'
  rw [cov.degree_eq u']
  exact hreg (cov.proj u')

include cov in
theorem card_edgeFinset_eq [Finite V'] [Finite V] [Fintype H'.edgeSet] [Fintype H.edgeSet] :
    H'.edgeFinset.card = m * H.edgeFinset.card := by
  classical
  have : Fintype V' := Fintype.ofFinite V'
  have : Fintype V := Fintype.ofFinite V
  have h1 : ∑ u' : V', H'.degree u' = 2 * H'.edgeFinset.card := by
    convert H'.sum_degrees_eq_twice_card_edges
  have h2 : ∑ u : V, H.degree u = 2 * H.edgeFinset.card := by
    convert H.sum_degrees_eq_twice_card_edges
  have hsum : ∑ u' : V', H'.degree u' = m * ∑ u : V, H.degree u := by
    calc ∑ u' : V', H'.degree u'
        = ∑ u' : V', H.degree (cov.proj u') :=
          Finset.sum_congr rfl fun u' _ => cov.degree_eq u'
      _ = ∑ u : V, ∑ _u' ∈ cov.fiber u, H.degree u := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := cov.proj)
            (fun u' _ => Finset.mem_univ (cov.proj u'))]
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' hu' => ?_
          rw [cov.mem_fiber.mp hu']
      _ = ∑ u : V, m * H.degree u :=
          Finset.sum_congr rfl fun u _ => by
            rw [Finset.sum_const, cov.card_fiber u, smul_eq_mul]
      _ = m * ∑ u : V, H.degree u := (Finset.mul_sum _ _ _).symm
  have hmul : 2 * H'.edgeFinset.card = 2 * (m * H.edgeFinset.card) := by
    rw [← h1, hsum, h2, ← mul_assoc, mul_comm m 2, mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left (by decide) hmul

include cov in
theorem ncard_edgeSet_eq [Finite V'] [Finite V] :
    H'.edgeSet.ncard = m * H.edgeSet.ncard := by
  classical
  have : Fintype V' := Fintype.ofFinite V'
  have : Fintype V := Fintype.ofFinite V
  rw [← H'.coe_edgeFinset, ← H.coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact cov.card_edgeFinset_eq

/-- Restriction of a covering map to the connected component `C` of a vertex `u₀' : V'` when the
base graph `H` is connected. Produces a connected covering graph with positive sheet count
`m₀ = |C ∩ proj⁻¹(proj u₀')| ≤ m`. -/
def restrictComponent [Finite V'] (hH : H.Connected) (u₀' : V') :
    SimpleGraphCover (H'.induce (H'.connectedComponentMk u₀').supp) H
      {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = cov.proj u₀'}.ncard where
  proj v' := cov.proj v'.1
  hm := by
    have hfin : {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧
        cov.proj v' = cov.proj u₀'}.Finite := Set.toFinite _
    rw [Set.ncard_pos hfin]
    exact ⟨u₀', rfl, rfl⟩
  card_fiber_set v := by
    have hcomp_eq : ∀ {x y : V}, H.Adj x y →
        {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = x}.ncard =
        {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = y}.ncard := by
      intro x y hxy
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      refine Nat.card_congr ?_
      refine
        { toFun := fun a =>
            ⟨(cov.fiberEquiv hxy ⟨a.1, a.2.2⟩).1,
              (SimpleGraph.ConnectedComponent.sound
                (cov.fiberEquiv_adj hxy ⟨a.1, a.2.2⟩).reachable).symm.trans a.2.1,
              (cov.fiberEquiv hxy ⟨a.1, a.2.2⟩).2⟩
          invFun := fun b =>
            ⟨((cov.fiberEquiv hxy).symm ⟨b.1, b.2.2⟩).1,
              (SimpleGraph.ConnectedComponent.sound
                (cov.fiberEquiv_symm_adj hxy ⟨b.1, b.2.2⟩).reachable).trans b.2.1,
              ((cov.fiberEquiv hxy).symm ⟨b.1, b.2.2⟩).2⟩
          left_inv := fun a => Subtype.ext (by
            dsimp only
            exact congrArg Subtype.val ((cov.fiberEquiv hxy).symm_apply_apply ⟨a.1, a.2.2⟩))
          right_inv := fun b => Subtype.ext (by
            dsimp only
            exact congrArg Subtype.val ((cov.fiberEquiv hxy).apply_symm_apply ⟨b.1, b.2.2⟩)) }
    have hwalk : ∀ {x y : V} (_w : H.Walk x y),
        {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = x}.ncard =
        {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = y}.ncard := by
      intro x y w
      induction w with
      | nil => rfl
      | cons hadj _ ih => exact (hcomp_eq hadj).trans ih
    have heq : {a : (H'.connectedComponentMk u₀').supp | cov.proj a.1 = v}.ncard =
        {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = v}.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
          invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, _, _⟩ => rfl }
    rw [heq]
    obtain ⟨w⟩ := hH v (cov.proj u₀')
    exact hwalk w
  adj_proj h := cov.adj_proj h
  lift_adj u' v hv := by
    let w' := cov.liftNeighbor u'.1 hv
    have hw_adj : H'.Adj u'.1 w' := cov.adj_liftNeighbor u'.1 hv
    have hw_mem : w' ∈ (H'.connectedComponentMk u₀').supp :=
      (SimpleGraph.ConnectedComponent.sound hw_adj.reachable).symm.trans u'.2
    refine ⟨⟨w', hw_mem⟩, ⟨cov.proj_liftNeighbor u'.1 hv, hw_adj⟩, ?_⟩
    rintro ⟨y', hy_mem⟩ ⟨hp, ha⟩
    exact Subtype.ext (cov.eq_liftNeighbor hv hp ha)

@[simp] theorem restrictComponent_proj [Finite V'] (hH : H.Connected) (u₀' : V')
    (v' : (H'.connectedComponentMk u₀').supp) :
    (cov.restrictComponent hH u₀').proj v' = cov.proj v'.1 := by
  rfl

theorem restrictComponent_sheet_le [Finite V'] (u₀' : V') :
    {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧ cov.proj v' = cov.proj u₀'}.ncard ≤ m := by
  have hsub : {v' : V' | v' ∈ (H'.connectedComponentMk u₀').supp ∧
      cov.proj v' = cov.proj u₀'} ⊆ {v' : V' | cov.proj v' = cov.proj u₀'} := fun _ h => h.2
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans_eq
    (cov.card_fiber_set (cov.proj u₀'))

end Basic

end SimpleGraphCover

/-! ### Bridge between `SimpleGraph` and `Multigraph` -/

section MultigraphBridge

variable {V : Type*} (H : SimpleGraph V)

/-- Canonical `Multigraph` whose edge set is `H.edgeSet` (with arbitrary choice of orientation via
`Quot.out`). -/
@[expose] noncomputable def ofSimpleGraph : Multigraph V H.edgeSet where
  src e := (Quot.out e.1).1
  tgt e := (Quot.out e.1).2

@[simp] theorem ofSimpleGraph_ends (e : H.edgeSet) :
    (ofSimpleGraph H).ends e = e.1 :=
  Quot.out_eq e.1

theorem ofSimpleGraph_ends_injective : Function.Injective (ofSimpleGraph H).ends := by
  intro e₁ e₂ h
  apply Subtype.ext
  simpa only [ofSimpleGraph_ends] using h

theorem ofSimpleGraph_loopless : (ofSimpleGraph H).Loopless := by
  intro e h
  have hmem := e.2
  have hends : s((ofSimpleGraph H).src e, (ofSimpleGraph H).tgt e) = e.1 := ofSimpleGraph_ends H e
  rw [← hends, h] at hmem
  exact H.loopless.irrefl _ hmem

@[simp] theorem toSimpleGraph_ofSimpleGraph : (ofSimpleGraph H).toSimpleGraph = H := by
  ext u v
  rw [Multigraph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, e, he⟩
    have hmem : s(u, v) ∈ H.edgeSet := by
      rw [← he, ofSimpleGraph_ends]
      exact e.2
    exact hmem
  · intro huv
    exact ⟨H.ne_of_adj huv, ⟨s(u, v), huv⟩, ofSimpleGraph_ends H _⟩

theorem ofSimpleGraph_incidenceSet_ncard (v : V) :
    ((ofSimpleGraph H).incidenceSet v).ncard = (H.neighborSet v).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  have hmem_iff : ∀ e : H.edgeSet, e ∈ (ofSimpleGraph H).incidenceSet v ↔ v ∈ e.1 := by
    intro e
    have hends : s((ofSimpleGraph H).src e, (ofSimpleGraph H).tgt e) = e.1 :=
      ofSimpleGraph_ends H e
    change ((ofSimpleGraph H).src e = v ∨ (ofSimpleGraph H).tgt e = v) ↔ v ∈ e.1
    rw [← hends, Sym2.mem_iff]
    exact or_congr eq_comm eq_comm
  refine Nat.card_congr
    { toFun := fun e =>
        ⟨Sym2.Mem.other ((hmem_iff e.1).mp e.2), by
          have hve : v ∈ e.1.1 := (hmem_iff e.1).mp e.2
          have heq : s(v, Sym2.Mem.other hve) = e.1.1 := Sym2.other_spec hve
          have hadj : s(v, Sym2.Mem.other hve) ∈ H.edgeSet := heq.symm ▸ e.1.2
          exact hadj⟩
      invFun := fun u =>
        ⟨⟨s(v, u.1), u.2⟩, (hmem_iff ⟨s(v, u.1), u.2⟩).mpr (by simp)⟩
      left_inv := fun e => by
        apply Subtype.ext; apply Subtype.ext
        exact Sym2.other_spec ((hmem_iff e.1).mp e.2)
      right_inv := fun u => by
        apply Subtype.ext
        have hve : v ∈ s(v, u.1) := by simp
        have hspec := Sym2.other_spec hve
        rcases Sym2.eq_iff.mp hspec with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact absurd h1 (H.ne_of_adj u.2) }

theorem ofSimpleGraph_maxDegreeLE_iff [Finite H.edgeSet] (d : ℕ) :
    (ofSimpleGraph H).MaxDegreeLE d ↔ ∀ v : V, (H.neighborSet v).ncard ≤ d := by
  simp only [Multigraph.MaxDegreeLE, ofSimpleGraph_incidenceSet_ncard]

end MultigraphBridge

/-! ### Exact crossing-cover lifting via König's theorem -/

section SimpleCrossingCover

variable {V : Type*}

/-- A `Finset V` is a crossing vertex cover of the simple graph `H` for bipartition `b : V → Bool`
if every edge joining vertices with distinct `b`-labels has at least one endpoint in `C`. -/
@[expose] def IsSimpleCrossingCover (H : SimpleGraph V) (b : V → Bool) (C : Finset V) : Prop :=
  ∀ u v : V, H.Adj u v → b u ≠ b v → u ∈ C ∨ v ∈ C

theorem isSimpleCrossingCover_univ [Fintype V] (H : SimpleGraph V) (b : V → Bool) :
    IsSimpleCrossingCover H b Finset.univ :=
  fun _ _ _ _ => Or.inl (Finset.mem_univ _)

/-- Minimum crossing vertex-cover cardinality of a simple graph `H` at bipartition `b`. -/
@[expose] noncomputable def simpleCrossingCover (H : SimpleGraph V) (b : V → Bool) : ℕ :=
  sInf {k : ℕ | ∃ C : Finset V, IsSimpleCrossingCover H b C ∧ C.card = k}

private theorem simpleCrossingCover_set_nonempty [Finite V] (H : SimpleGraph V) (b : V → Bool) :
    {k : ℕ | ∃ C : Finset V, IsSimpleCrossingCover H b C ∧ C.card = k}.Nonempty := by
  have := Fintype.ofFinite V
  exact ⟨(Finset.univ : Finset V).card, Finset.univ, isSimpleCrossingCover_univ H b, rfl⟩

theorem simpleCrossingCover_le_card {H : SimpleGraph V} {b : V → Bool} {C : Finset V}
    (hC : IsSimpleCrossingCover H b C) :
    simpleCrossingCover H b ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

theorem exists_minSimpleCrossingCover [Finite V] (H : SimpleGraph V) (b : V → Bool) :
    ∃ C : Finset V, IsSimpleCrossingCover H b C ∧ C.card = simpleCrossingCover H b :=
  Nat.sInf_mem (simpleCrossingCover_set_nonempty H b)

/-- Crossing vertex covers of a multigraph `G` coincide with crossing vertex covers of its
underlying simple graph `G.toSimpleGraph` (loops never cross, and parallel edges impose identical
constraints). -/
theorem isSimpleCrossingCover_toSimpleGraph_iff {E : Type*} (G : Multigraph V E)
    (b : V → Bool) (C : Finset V) :
    IsSimpleCrossingCover G.toSimpleGraph b C ↔ IsCrossingCover G b C := by
  constructor
  · intro hC e hne
    have hne_v : G.src e ≠ G.tgt e := fun heq => hne (congrArg b heq)
    exact hC (G.src e) (G.tgt e) (Multigraph.toSimpleGraph_adj.mpr ⟨hne_v, e, rfl⟩) hne
  · intro hC u v hadj hne
    obtain ⟨_, e, he⟩ := Multigraph.toSimpleGraph_adj.mp hadj
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2] at hne ⊢
      exact hC e hne
    · rw [← h1, ← h2] at hne ⊢
      exact (hC e hne.symm).symm

/-- For every multigraph `G`, `simpleCrossingCover G.toSimpleGraph b = crossingCover G b`. -/
theorem simpleCrossingCover_toSimpleGraph {E : Type*} (G : Multigraph V E) (b : V → Bool) :
    simpleCrossingCover G.toSimpleGraph b = crossingCover G b := by
  unfold simpleCrossingCover crossingCover
  congr 1; ext k
  exact exists_congr fun C => and_congr_left' (isSimpleCrossingCover_toSimpleGraph_iff G b C)

theorem crossingCover_ofSimpleGraph (H : SimpleGraph V) (b : V → Bool) :
    crossingCover (ofSimpleGraph H) b = simpleCrossingCover H b := by
  rw [← simpleCrossingCover_toSimpleGraph (ofSimpleGraph H) b, toSimpleGraph_ofSimpleGraph]

/-- **König's theorem for crossing graphs:** every finite simple graph `H` and bipartition
`b : V → Bool` admit a crossing matching `M` (edges directed from `b = false` to `b = true`, with
pairwise disjoint left and right endpoints) whose cardinality equals `simpleCrossingCover H b`. -/
theorem exists_crossingMatching_eq_simpleCrossingCover [Finite V]
    (H : SimpleGraph V) (b : V → Bool) :
    ∃ M : Finset (V × V),
      (∀ e ∈ M, H.Adj e.1 e.2 ∧ b e.1 = false ∧ b e.2 = true) ∧
      (∀ u v₁ v₂, (u, v₁) ∈ M → (u, v₂) ∈ M → v₁ = v₂) ∧
      (∀ u₁ u₂ v, (u₁, v) ∈ M → (u₂, v) ∈ M → u₁ = u₂) ∧
      M.card = simpleCrossingCover H b := by
  classical
  have := Fintype.ofFinite V
  let L := {v : V // b v = false}
  let R := {v : V // b v = true}
  let bg : L × R → Bool := fun p => decide (H.Adj p.1.1 p.2.1)
  obtain ⟨M₀, K, hM₀, hK, hcard⟩ :=
    Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover bg
  have hK_eq : K.size = simpleCrossingCover H b := by
    apply le_antisymm
    · obtain ⟨C₀, hC₀, hC₀_card⟩ := exists_minSimpleCrossingCover H b
      let K₀ : Cslib.Algorithms.Lean.MaxFlow.VertexCover L R :=
        { left := Finset.univ.filter fun u : L => u.1 ∈ C₀
          right := Finset.univ.filter fun v : R => v.1 ∈ C₀ }
      have hK₀_vc : Cslib.Algorithms.Lean.MaxFlow.IsVertexCover bg K₀ := by
        intro u v hbg
        have hadj : H.Adj u.1 v.1 := by simpa [bg] using hbg
        have hne : b u.1 ≠ b v.1 := by rw [u.2, v.2]; decide
        rcases hC₀ u.1 v.1 hadj hne with hu | hv
        · exact Or.inl (by simp [K₀, hu])
        · exact Or.inr (by simp [K₀, hv])
      have hL_card : K₀.left.card = (C₀.filter fun v => b v = false).card := by
        refine Finset.card_bij (fun u _ => u.1) ?_ ?_ ?_
        · intro u hu
          have hu' : u.1 ∈ C₀ := (Finset.mem_filter.mp hu).2
          exact Finset.mem_filter.mpr ⟨hu', u.2⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro v hv
          rw [Finset.mem_filter] at hv
          exact ⟨⟨v, hv.2⟩, by simp [K₀, hv.1], rfl⟩
      have hR_card : K₀.right.card = (C₀.filter fun v => b v = true).card := by
        refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
        · intro v hv
          have hv' : v.1 ∈ C₀ := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨hv', v.2⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro v hv
          rw [Finset.mem_filter] at hv
          exact ⟨⟨v, hv.2⟩, by simp [K₀, hv.1], rfl⟩
      have hpart : (C₀.filter fun v => b v = false).card +
          (C₀.filter fun v => b v = true).card = C₀.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter]
          cases bv : b v <;> simp
        · rw [Finset.disjoint_left]
          intro v h1 h2
          rw [Finset.mem_filter] at h1 h2
          exact Bool.false_ne_true (h1.2.symm.trans h2.2)
      have hle := hK.2 K₀ hK₀_vc
      change K.size ≤ K₀.left.card + K₀.right.card at hle
      omega
    · let embL : L ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      let embR : R ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      let C : Finset V := K.left.map embL ∪ K.right.map embR
      have hdisj : Disjoint (K.left.map embL) (K.right.map embR) := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp h1
        obtain ⟨w, _, heq⟩ := Finset.mem_map.mp h2
        change w.1 = u.1 at heq
        exact Bool.false_ne_true (u.2.symm.trans (heq ▸ w.2))
      have hC_cov : IsSimpleCrossingCover H b C := by
        intro u v hadj hne
        cases hu : b u <;> cases hv : b v
        · exact (hne (hu.trans hv.symm)).elim
        · have hbg : bg (⟨u, hu⟩, ⟨v, hv⟩) = true := by simp [bg, hadj]
          rcases hK.1 ⟨u, hu⟩ ⟨v, hv⟩ hbg with h1 | h2
          · exact Or.inl (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨u, hu⟩, h1, rfl⟩))
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨⟨v, hv⟩, h2, rfl⟩))
        · have hbg : bg (⟨v, hv⟩, ⟨u, hu⟩) = true := by simp [bg, hadj.symm]
          rcases hK.1 ⟨v, hv⟩ ⟨u, hu⟩ hbg with h1 | h2
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨v, hv⟩, h1, rfl⟩))
          · exact Or.inl (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨⟨u, hu⟩, h2, rfl⟩))
        · exact (hne (hu.trans hv.symm)).elim
      calc simpleCrossingCover H b ≤ C.card := simpleCrossingCover_le_card hC_cov
        _ = (K.left.map embL).card + (K.right.map embR).card :=
            Finset.card_union_of_disjoint hdisj
        _ = K.left.card + K.right.card := by simp
        _ = K.size := rfl
  let embLR : L × R ↪ V × V :=
    ⟨fun p => (p.1.1, p.2.1), fun a b h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)⟩
  refine ⟨M₀.map embLR, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨⟨u, v⟩, hm, rfl⟩ := Finset.mem_map.mp he
    have hbg : bg (u, v) = true := hM₀.1.1 (u, v) hm
    change H.Adj u.1 v.1 ∧ b u.1 = false ∧ b v.1 = true
    exact ⟨by simpa [bg] using hbg, u.2, v.2⟩
  · intro u v₁ v₂ h1 h2
    obtain ⟨⟨u₁, w₁⟩, hm₁, he₁⟩ := Finset.mem_map.mp h1
    obtain ⟨⟨u₂, w₂⟩, hm₂, he₂⟩ := Finset.mem_map.mp h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₁
    obtain ⟨hu, rfl⟩ := Prod.mk.inj he₂
    have hu' : u₁ = u₂ := Subtype.ext hu.symm
    subst hu'
    exact congrArg Subtype.val (hM₀.1.2.1 u₁ w₁ w₂ hm₁ hm₂)
  · intro u₁ u₂ v h1 h2
    obtain ⟨⟨w₁, v₁⟩, hm₁, he₁⟩ := Finset.mem_map.mp h1
    obtain ⟨⟨w₂, v₂⟩, hm₂, he₂⟩ := Finset.mem_map.mp h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he₁
    obtain ⟨rfl, hv⟩ := Prod.mk.inj he₂
    have hv' : v₁ = v₂ := Subtype.ext hv.symm
    subst hv'
    exact congrArg Subtype.val (hM₀.1.2.2 w₁ w₂ v₁ hm₁ hm₂)
  · rw [Finset.card_map, hcard, hK_eq]

/-- **Exact crossing-cover lifting theorem:** if `cov : SimpleGraphCover H' H m` is a finite
`m`-sheeted covering map, then lifting a vertex bipartition `b : V → Bool` to `b ∘ cov.proj`
scales the minimum crossing vertex-cover size by exact factor `m`. -/
theorem simpleCrossingCover_lift_eq {V' : Type*} [Finite V'] [Finite V]
    {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
    (cov : SimpleGraphCover H' H m) (b : V → Bool) :
    simpleCrossingCover H' (b ∘ cov.proj) = m * simpleCrossingCover H b := by
  classical
  have := Fintype.ofFinite V'
  have := Fintype.ofFinite V
  apply le_antisymm
  · obtain ⟨C, hC, hC_card⟩ := exists_minSimpleCrossingCover H b
    let C' : Finset V' := C.biUnion fun v => cov.fiber v
    have hC'_cov : IsSimpleCrossingCover H' (b ∘ cov.proj) C' := by
      intro u' v' hadj hne
      rcases hC (cov.proj u') (cov.proj v') (cov.adj_proj hadj) hne with hu | hv
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨cov.proj u', hu, by simp [cov.mem_fiber]⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨cov.proj v', hv, by simp [cov.mem_fiber]⟩)
    have hdisj : Set.PairwiseDisjoint (C : Set V) fun v => cov.fiber v :=
      fun u _ v _ hne => cov.disjoint_fiber hne
    calc simpleCrossingCover H' (b ∘ cov.proj)
        ≤ C'.card := simpleCrossingCover_le_card hC'_cov
      _ = ∑ v ∈ C, (cov.fiber v).card := Finset.card_biUnion hdisj
      _ = ∑ _v ∈ C, m := Finset.sum_congr rfl fun v _ => cov.card_fiber v
      _ = C.card * m := by simp
      _ = m * simpleCrossingCover H b := by rw [hC_card, Nat.mul_comm]
  · obtain ⟨C', hC', hC'_card⟩ := exists_minSimpleCrossingCover H' (b ∘ cov.proj)
    obtain ⟨M, hM_edge, hM_left, hM_right, hM_card⟩ :=
      exists_crossingMatching_eq_simpleCrossingCover H b
    have hpair : ∀ e ∈ M,
        m ≤ (C' ∩ cov.fiber e.1).card + (C' ∩ cov.fiber e.2).card := by
      intro e he
      obtain ⟨hadj, hbu, hbv⟩ := hM_edge e he
      let α := {u' : V' // cov.proj u' = e.1}
      let β := {v' : V' // cov.proj v' = e.2}
      let φ : α ≃ β := cov.fiberEquiv hadj
      have hcard_α : Fintype.card α = m := cov.card_subtype_fiber e.1
      have hcov_pt : ∀ u' : α,
          1 ≤ (if u'.1 ∈ C' then 1 else 0) + (if (φ u').1 ∈ C' then 1 else 0) := by
        intro u'
        have hadj' : H'.Adj u'.1 (φ u').1 := cov.fiberEquiv_adj hadj u'
        have hne : (b ∘ cov.proj) u'.1 ≠ (b ∘ cov.proj) (φ u').1 := by
          simp only [Function.comp_apply, u'.2, (φ u').2, hbu, hbv]
          decide
        rcases hC' u'.1 (φ u').1 hadj' hne with h1 | h2
        · simp [h1]
        · simp [h2]
      have hsum_fiber : ∀ v : V,
          ∑ u' : {x : V' // cov.proj x = v}, (if u'.1 ∈ C' then 1 else 0) =
            (C' ∩ cov.fiber v).card := fun v => by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        refine Finset.card_bij (fun u' _ => u'.1) ?_ ?_ ?_
        · intro u' hu'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu'
          exact Finset.mem_inter.mpr ⟨hu', cov.mem_fiber.mpr u'.2⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro x hx
          obtain ⟨hxC, hxf⟩ := Finset.mem_inter.mp hx
          exact ⟨⟨x, cov.mem_fiber.mp hxf⟩, by simp [hxC], rfl⟩
      calc m = Fintype.card α := hcard_α.symm
        _ = ∑ _u' : α, (1 : ℕ) := by simp
        _ ≤ ∑ u' : α, ((if u'.1 ∈ C' then 1 else 0) + (if (φ u').1 ∈ C' then 1 else 0)) :=
            Finset.sum_le_sum fun u' _ => hcov_pt u'
        _ = (∑ u' : α, (if u'.1 ∈ C' then 1 else 0)) +
            (∑ u' : α, (if (φ u').1 ∈ C' then 1 else 0)) := Finset.sum_add_distrib
        _ = (∑ u' : α, (if u'.1 ∈ C' then 1 else 0)) +
            (∑ v' : β, (if v'.1 ∈ C' then 1 else 0)) := by
            congr 1; exact Fintype.sum_equiv φ _ _ fun _ => rfl
        _ = (C' ∩ cov.fiber e.1).card + (C' ∩ cov.fiber e.2).card := by
            rw [hsum_fiber e.1, hsum_fiber e.2]
    have hinj1 : Set.InjOn Prod.fst (M : Set (V × V)) := fun a ha b hb h =>
      Prod.ext h (hM_left a.1 a.2 b.2 ha (h ▸ hb))
    have hinj2 : Set.InjOn Prod.snd (M : Set (V × V)) := fun a ha b hb h =>
      Prod.ext (hM_right a.1 b.1 a.2 ha (h ▸ hb)) h
    have hdisj : Disjoint (M.image Prod.fst) (M.image Prod.snd) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨e₂, he₂, h2eq⟩ := Finset.mem_image.mp h2
      have hb1 := (hM_edge e₁ he₁).2.1
      have hb2 := (hM_edge e₂ he₂).2.2
      rw [h2eq] at hb2
      exact Bool.false_ne_true (hb1.symm.trans hb2)
    have hC'_sum : ∑ v : V, (C' ∩ cov.fiber v).card = C'.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := cov.proj) (fun x _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun v _ => congrArg Finset.card ?_
      ext x; simp [cov.mem_fiber]
    calc m * simpleCrossingCover H b
        = M.card * m := by rw [hM_card, Nat.mul_comm]
      _ = ∑ _e ∈ M, m := by simp
      _ ≤ ∑ e ∈ M, ((C' ∩ cov.fiber e.1).card + (C' ∩ cov.fiber e.2).card) :=
          Finset.sum_le_sum hpair
      _ = (∑ e ∈ M, (C' ∩ cov.fiber e.1).card) + (∑ e ∈ M, (C' ∩ cov.fiber e.2).card) :=
          Finset.sum_add_distrib
      _ = (∑ v ∈ M.image Prod.fst, (C' ∩ cov.fiber v).card) +
          (∑ v ∈ M.image Prod.snd, (C' ∩ cov.fiber v).card) := by
          rw [Finset.sum_image (f := fun v => (C' ∩ cov.fiber v).card) hinj1,
              Finset.sum_image (f := fun v => (C' ∩ cov.fiber v).card) hinj2]
      _ = ∑ v ∈ M.image Prod.fst ∪ M.image Prod.snd, (C' ∩ cov.fiber v).card :=
          (Finset.sum_union hdisj).symm
      _ ≤ ∑ v : V, (C' ∩ cov.fiber v).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = C'.card := hC'_sum
      _ = simpleCrossingCover H' (b ∘ cov.proj) := hC'_card

/-- Multigraph variant of `simpleCrossingCover_lift_eq`: if the underlying simple graphs are linked
by a finite `m`-sheeted covering map `cov`, then `crossingCover` lifts by factor `m`. -/
theorem crossingCover_lift_eq {V' E' E : Type*} [Finite V'] [Finite V]
    {G' : Multigraph V' E'} {G : Multigraph V E} {m : ℕ}
    (cov : SimpleGraphCover G'.toSimpleGraph G.toSimpleGraph m) (b : V → Bool) :
    crossingCover G' (b ∘ cov.proj) = m * crossingCover G b := by
  rw [← simpleCrossingCover_toSimpleGraph G', ← simpleCrossingCover_toSimpleGraph G]
  exact simpleCrossingCover_lift_eq cov b

/-- Corollary of `simpleCrossingCover_lift_eq` for canonical `ofSimpleGraph` multigraphs. -/
theorem crossingCover_ofSimpleGraph_lift_eq {V' : Type*} [Finite V'] [Finite V]
    {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
    (cov : SimpleGraphCover H' H m) (b : V → Bool) :
    crossingCover (ofSimpleGraph H') (b ∘ cov.proj) = m * crossingCover (ofSimpleGraph H) b := by
  rw [crossingCover_ofSimpleGraph, crossingCover_ofSimpleGraph]
  exact simpleCrossingCover_lift_eq cov b

end SimpleCrossingCover

/-! ### Non-backtracking walks and local-tree uniqueness -/

section NonBacktrackingWalk

/-- A **non-backtracking walk** of length `j` in a simple graph `H`: consecutive vertices are
adjacent in `H`, and no two steps immediately reverse (`w i ≠ w (i + 2)`). -/
@[expose] def IsNBWalk {V : Type*} (H : SimpleGraph V) (j : ℕ) (w : Fin (j + 1) → V) : Prop :=
  (∀ i : Fin j, H.Adj (w i.castSucc) (w i.succ)) ∧
    ∀ i : ℕ, (h : i + 2 ≤ j) → w ⟨i, by omega⟩ ≠ w ⟨i + 2, by omega⟩

namespace IsNBWalk

variable {V : Type*} {H : SimpleGraph V}

theorem adj_step {j : ℕ} {w : Fin (j + 1) → V} (hw : IsNBWalk H j w)
    {i : ℕ} (hi : i < j) :
    H.Adj (w ⟨i, by omega⟩) (w ⟨i + 1, by omega⟩) :=
  hw.1 ⟨i, hi⟩

theorem ne_two_step {j : ℕ} {w : Fin (j + 1) → V} (hw : IsNBWalk H j w)
    {i : ℕ} (hi : i + 2 ≤ j) :
    w ⟨i, by omega⟩ ≠ w ⟨i + 2, by omega⟩ :=
  hw.2 i hi

/-- The image of a non-backtracking walk under a covering projection is non-backtracking. -/
theorem map_cover {V' : Type*} {H' : SimpleGraph V'} {m : ℕ}
    (cov : SimpleGraphCover H' H m) {j : ℕ} {w' : Fin (j + 1) → V'}
    (hw' : IsNBWalk H' j w') :
    IsNBWalk H j (cov.proj ∘ w') := by
  refine ⟨fun i => cov.adj_proj (hw'.1 i), fun i hi hpeq => ?_⟩
  have h1 : H'.Adj (w' ⟨i + 1, by omega⟩) (w' ⟨i, by omega⟩) :=
    (hw'.adj_step (i := i) (by omega)).symm
  have h2 : H'.Adj (w' ⟨i + 1, by omega⟩) (w' ⟨i + 2, by omega⟩) :=
    hw'.adj_step (i := i + 1) (by omega)
  exact hw'.ne_two_step hi (cov.eq_of_adj_of_proj_eq h1 h2 hpeq)

/-- Drop the first vertex from a non-backtracking walk of length `j + 1`. -/
theorem tail {j : ℕ} {w : Fin (j + 2) → V} (hw : IsNBWalk H (j + 1) w) :
    IsNBWalk H j (fun i => w i.succ) := by
  refine ⟨fun i => hw.adj_step (by omega), fun i hi => ?_⟩
  exact hw.ne_two_step (i := i + 1) (by omega)

/-- Drop the last vertex from a non-backtracking walk of length `j + 1`. -/
theorem init {j : ℕ} {w : Fin (j + 2) → V} (hw : IsNBWalk H (j + 1) w) :
    IsNBWalk H j (fun i => w i.castSucc) := by
  refine ⟨fun i => hw.adj_step (by omega), fun i hi => ?_⟩
  exact hw.ne_two_step (i := i) (by omega)

/-- A non-backtracking walk in an induced subgraph maps to a non-backtracking walk in the ambient
graph. -/
theorem map_induce {S : Set V} {j : ℕ} {w : Fin (j + 1) → S}
    (hw : IsNBWalk (H.induce S) j w) :
    IsNBWalk H j (Subtype.val ∘ w) :=
  ⟨fun i => hw.1 i, fun i hi heq => hw.2 i hi (Subtype.ext heq)⟩

/-- Concatenate `w₁` with the reverse of `w₂` when they meet at their last vertices with distinct
penultimate vertices, forming a non-backtracking walk from `w₁ 0` to `w₂ 0`. -/
private theorem concat_rev {j₁ j₂ : ℕ} {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (h1 : IsNBWalk H j₁ w₁) (h2 : IsNBWalk H j₂ w₂)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂)
    (hend : w₁ ⟨j₁, by omega⟩ = w₂ ⟨j₂, by omega⟩)
    (hpen : w₁ ⟨j₁ - 1, by omega⟩ ≠ w₂ ⟨j₂ - 1, by omega⟩) :
    ∃ w : Fin (j₁ + j₂ + 1) → V,
      IsNBWalk H (j₁ + j₂) w ∧ w 0 = w₁ 0 ∧ w (Fin.last (j₁ + j₂)) = w₂ 0 := by
  let w : Fin (j₁ + j₂ + 1) → V := fun i =>
    if hi : i.1 ≤ j₁ then w₁ ⟨i.1, by omega⟩ else w₂ ⟨j₁ + j₂ - i.1, by omega⟩
  have hw_le : ∀ (k : ℕ) (hk : k ≤ j₁), w ⟨k, by omega⟩ = w₁ ⟨k, by omega⟩ := fun k hk => by
    simp [w, hk]
  have hw_ge : ∀ (k : ℕ) (hk1 : j₁ ≤ k) (hk2 : k ≤ j₁ + j₂),
      w ⟨k, by omega⟩ = w₂ ⟨j₁ + j₂ - k, by omega⟩ := by
    intro k hk1 hk2
    by_cases heq : k = j₁
    · subst heq
      simp only [w, le_refl, ↓reduceDIte]
      simpa [Nat.add_sub_cancel_left] using hend
    · have hnot : ¬(k ≤ j₁) := by omega
      simp [w, hnot]
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    by_cases hlt : i + 1 ≤ j₁
    · rw [show (⟨i, hi⟩ : Fin (j₁ + j₂)).castSucc = ⟨i, by omega⟩ from rfl,
          show (⟨i, hi⟩ : Fin (j₁ + j₂)).succ = ⟨i + 1, by omega⟩ from rfl,
          hw_le i (by omega), hw_le (i + 1) hlt]
      exact h1.adj_step (by omega)
    · have hge : j₁ ≤ i := by omega
      rw [show (⟨i, hi⟩ : Fin (j₁ + j₂)).castSucc = ⟨i, by omega⟩ from rfl,
          show (⟨i, hi⟩ : Fin (j₁ + j₂)).succ = ⟨i + 1, by omega⟩ from rfl,
          hw_ge i hge (by omega), hw_ge (i + 1) (by omega) (by omega)]
      have hadj := h2.adj_step (i := j₁ + j₂ - (i + 1)) (by omega)
      have hidx : j₁ + j₂ - (i + 1) + 1 = j₁ + j₂ - i := by omega
      rw [show (⟨j₁ + j₂ - i, by omega⟩ : Fin (j₂ + 1)) =
        ⟨j₁ + j₂ - (i + 1) + 1, by omega⟩ from Fin.ext hidx.symm]
      exact hadj.symm
  · intro i hi
    rcases lt_or_ge (i + 2) (j₁ + 1) with hle | hgt
    · rw [hw_le i (by omega), hw_le (i + 2) (by omega)]
      exact h1.ne_two_step (by omega)
    · rcases lt_or_ge i j₁ with hlt | hge
      · have hmid : i = j₁ - 1 := by omega
        rw [hw_le i (by omega), hw_ge (i + 2) (by omega) (by omega)]
        have hi1 : (⟨i, by omega⟩ : Fin (j₁ + 1)) = ⟨j₁ - 1, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have hi2 : (⟨j₁ + j₂ - (i + 2), by omega⟩ : Fin (j₂ + 1)) = ⟨j₂ - 1, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hi1, hi2]
        exact hpen
      · rw [hw_ge i hge (by omega), hw_ge (i + 2) (by omega) (by omega)]
        have hnb := h2.ne_two_step (i := j₁ + j₂ - (i + 2)) (by omega)
        have ha : (⟨j₁ + j₂ - i, by omega⟩ : Fin (j₂ + 1)) =
            ⟨j₁ + j₂ - (i + 2) + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [ha]
        exact hnb.symm
  · exact hw_le 0 (Nat.zero_le _)
  · simpa [Fin.last] using hw_ge (j₁ + j₂) (by omega) le_rfl

/-- In any simple graph with no closed non-backtracking walk of length `1 ≤ j ≤ 2 * r`, two
non-backtracking walks of length at most `r` that share both endpoints must have equal length and
identical vertex sequences. -/
theorem eq_of_no_closed {r : ℕ}
    (hgirth : ∀ (j : ℕ), 1 ≤ j → j ≤ 2 * r →
      ∀ w : Fin (j + 1) → V, IsNBWalk H j w → w 0 ≠ w (Fin.last j))
    {j₁ j₂ : ℕ} (hj₁ : j₁ ≤ r) (hj₂ : j₂ ≤ r)
    {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (h1 : IsNBWalk H j₁ w₁) (h2 : IsNBWalk H j₂ w₂)
    (hstart : w₁ 0 = w₂ 0) (hend : w₁ (Fin.last j₁) = w₂ (Fin.last j₂)) :
    ∃ hlen : j₁ = j₂, ∀ i : ℕ, (hi : i ≤ j₁) → w₁ ⟨i, by omega⟩ = w₂ ⟨i, by omega⟩ := by
  have hmain : ∀ s : ℕ, ∀ (j₁ j₂ : ℕ), j₁ + j₂ = s → j₁ ≤ r → j₂ ≤ r →
      ∀ (w₁ : Fin (j₁ + 1) → V) (w₂ : Fin (j₂ + 1) → V),
        IsNBWalk H j₁ w₁ → IsNBWalk H j₂ w₂ →
        w₁ 0 = w₂ 0 → w₁ (Fin.last j₁) = w₂ (Fin.last j₂) →
        ∃ _ : j₁ = j₂, ∀ i : ℕ, (hi : i ≤ j₁) → w₁ ⟨i, by omega⟩ = w₂ ⟨i, by omega⟩ := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro j₁ j₂ hsum hj₁' hj₂' w₁ w₂ h1' h2' hs he
      rcases j₁ with _ | j₁'
      · rcases j₂ with _ | j₂'
        · refine ⟨rfl, fun i hi => ?_⟩
          have hi0 : i = 0 := by omega
          subst hi0; exact hs
        · exfalso
          exact hgirth (j₂' + 1) (by omega) (by omega) w₂ h2' (hs.symm.trans he)
      · rcases j₂ with _ | j₂'
        · exfalso
          exact hgirth (j₁' + 1) (by omega) (by omega) w₁ h1' (hs.trans he.symm)
        · by_cases hpen : w₁ ⟨j₁', by omega⟩ = w₂ ⟨j₂', by omega⟩
          · obtain ⟨hlen, hfn⟩ := ih (j₁' + j₂') (by omega) j₁' j₂' rfl (by omega) (by omega)
              (fun i => w₁ i.castSucc) (fun i => w₂ i.castSucc) h1'.init h2'.init hs hpen
            refine ⟨by omega, fun i hi => ?_⟩
            by_cases hlast : i = j₁' + 1
            · subst hlast
              simpa [Fin.last, hlen] using he
            · exact hfn i (by omega)
          · exfalso
            obtain ⟨w, hw, hw0, hwl⟩ :=
              concat_rev h1' h2' (by omega) (by omega) he hpen
            exact hgirth ((j₁' + 1) + (j₂' + 1)) (by omega) (by omega) w hw
              (hw0.trans (hs.trans hwl.symm))
  exact hmain (j₁ + j₂) j₁ j₂ rfl hj₁ hj₂ w₁ w₂ h1 h2 hstart hend

end IsNBWalk

namespace SimpleGraphCover

variable {V' V : Type*} {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
  (cov : SimpleGraphCover H' H m)

/-- Unique lifting of a base walk step-by-step from a given starting vertex `u' : V'`. -/
noncomputable def liftWalkAux (u' : V') :
    ∀ (j : ℕ) (w : Fin (j + 1) → V),
      w 0 = cov.proj u' → (∀ i : Fin j, H.Adj (w i.castSucc) (w i.succ)) →
        { w' : Fin (j + 1) → V' //
          w' 0 = u' ∧ (∀ k : Fin (j + 1), cov.proj (w' k) = w k) ∧
            ∀ i : Fin j, H'.Adj (w' i.castSucc) (w' i.succ) }
  | 0, w, h0, _ =>
    ⟨fun _ => u', rfl, fun k => by
      have hk : k = 0 := Fin.ext (by omega)
      subst hk; exact h0.symm, fun i => i.elim0⟩
  | j + 1, w, h0, hadj =>
    let ⟨prevW, hprev0, hprevProj, hprevAdj⟩ :=
      liftWalkAux u' j (fun i => w i.castSucc) h0 (fun i => hadj i.castSucc)
    let last := prevW (Fin.last j)
    have hproj_last : cov.proj last = w (Fin.last j).castSucc := hprevProj (Fin.last j)
    have hadj_last : H.Adj (cov.proj last) (w (Fin.last (j + 1))) := by
      rw [hproj_last]
      exact hadj (Fin.last j)
    let next := cov.liftNeighbor last hadj_last
    ⟨Fin.snoc prevW next, by simp [Fin.snoc, hprev0],
      fun k => by
        by_cases hk : k.1 < j + 1
        · have : k = (⟨k.1, hk⟩ : Fin (j + 1)).castSucc := Fin.ext rfl
          rw [this, Fin.snoc_castSucc]
          exact hprevProj ⟨k.1, hk⟩
        · have hkl : k = Fin.last (j + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [hkl, Fin.snoc_last]
          exact cov.proj_liftNeighbor last hadj_last,
      fun i => by
        by_cases hi : i.1 < j
        · have hc : i.castSucc = (⟨i.1, hi⟩ : Fin j).castSucc.castSucc := Fin.ext rfl
          have hs : i.succ = (⟨i.1, hi⟩ : Fin j).succ.castSucc := Fin.ext rfl
          rw [hc, hs, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hprevAdj ⟨i.1, hi⟩
        · have hil : i = Fin.last j := Fin.ext (by simp only [Fin.val_last]; omega)
          subst hil
          have hc : (Fin.last j : Fin (j + 1)).castSucc = (Fin.last j).castSucc := rfl
          have hs : (Fin.last j : Fin (j + 1)).succ = Fin.last (j + 1) := by
            ext; simp [Fin.last]
          rw [hs, Fin.snoc_castSucc, Fin.snoc_last]
          exact cov.adj_liftNeighbor last hadj_last⟩

/-- Uniqueness of a lifted walk with prescribed start vertex `u'` and base projection `w`. -/
theorem liftWalk_unique {u' : V'} {j : ℕ} {w₁' w₂' : Fin (j + 1) → V'}
    (h1_adj : ∀ i : Fin j, H'.Adj (w₁' i.castSucc) (w₁' i.succ))
    (h2_adj : ∀ i : Fin j, H'.Adj (w₂' i.castSucc) (w₂' i.succ))
    (hstart : w₁' 0 = u') (hstart₂ : w₂' 0 = u')
    (hproj : ∀ k : Fin (j + 1), cov.proj (w₁' k) = cov.proj (w₂' k)) :
    w₁' = w₂' := by
  ext k
  rcases k with ⟨k, hk⟩
  induction k with
  | zero => exact hstart.trans hstart₂.symm
  | succ k ih =>
    have heq := ih (by omega)
    have ha1 : H'.Adj (w₁' ⟨k, by omega⟩) (w₁' ⟨k + 1, hk⟩) := h1_adj ⟨k, by omega⟩
    have ha2 : H'.Adj (w₁' ⟨k, by omega⟩) (w₂' ⟨k + 1, hk⟩) := heq ▸ h2_adj ⟨k, by omega⟩
    exact cov.eq_of_adj_of_proj_eq ha1 ha2 (hproj ⟨k + 1, hk⟩)

/-- Every non-backtracking walk in `H` starting at `cov.proj u'` lifts uniquely to a
non-backtracking walk in `H'` starting at `u'`. -/
theorem existsUnique_lift_nbWalk (u' : V') {j : ℕ} {w : Fin (j + 1) → V}
    (hw : IsNBWalk H j w) (h0 : w 0 = cov.proj u') :
    ∃! w' : Fin (j + 1) → V',
      IsNBWalk H' j w' ∧ w' 0 = u' ∧ cov.proj ∘ w' = w := by
  let lifted := cov.liftWalkAux u' j w h0 hw.1
  have hnb : IsNBWalk H' j lifted.1 := by
    refine ⟨lifted.2.2.2, fun i hi heq => hw.ne_two_step hi ?_⟩
    rw [← lifted.2.2.1 ⟨i, by omega⟩, ← lifted.2.2.1 ⟨i + 2, by omega⟩, heq]
  refine ⟨lifted.1, ⟨hnb, lifted.2.1, funext lifted.2.2.1⟩, ?_⟩
  rintro w' ⟨hw', hw0, hwp⟩
  refine cov.liftWalk_unique hw'.1 lifted.2.2.2 hw0 lifted.2.1 fun k => ?_
  rw [show cov.proj (w' k) = (cov.proj ∘ w') k from rfl, hwp, lifted.2.2.1 k]

end SimpleGraphCover

/-- **Local-tree injectivity on balls of radius `r`:** in a covering graph `H'` with no closed
non-backtracking walk of length `1 ≤ j ≤ 2 * r + 1`, any two non-backtracking walks of length at
most `r` starting at `u' : V'` and ending at the same vertex in `H'` must coincide (so both walks
have the same length and identical vertices, and their projections to `H` coincide too). -/
theorem lift_nbWalk_injective_ball {V' V : Type*} {H' : SimpleGraph V'} {H : SimpleGraph V}
    {m r : ℕ} (cov : SimpleGraphCover H' H m)
    (hgirth : ∀ (j : ℕ), 1 ≤ j → j ≤ 2 * r + 1 →
      ∀ w' : Fin (j + 1) → V', IsNBWalk H' j w' → w' 0 ≠ w' (Fin.last j))
    {u' : V'} {j₁ j₂ : ℕ} (hj₁ : j₁ ≤ r) (hj₂ : j₂ ≤ r)
    {w₁' : Fin (j₁ + 1) → V'} {w₂' : Fin (j₂ + 1) → V'}
    (h1 : IsNBWalk H' j₁ w₁') (h2 : IsNBWalk H' j₂ w₂')
    (hstart₁ : w₁' 0 = u') (hstart₂ : w₂' 0 = u')
    (hend : w₁' (Fin.last j₁) = w₂' (Fin.last j₂)) :
    ∃ _ : j₁ = j₂, ∀ i : ℕ, (hi : i ≤ j₁) →
      w₁' ⟨i, by omega⟩ = w₂' ⟨i, by omega⟩ ∧
        cov.proj (w₁' ⟨i, by omega⟩) = cov.proj (w₂' ⟨i, by omega⟩) := by
  have hg : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * r →
      ∀ w' : Fin (j + 1) → V', IsNBWalk H' j w' → w' 0 ≠ w' (Fin.last j) :=
    fun j hlo hhi => hgirth j hlo (by omega)
  obtain ⟨hlen, heq⟩ := IsNBWalk.eq_of_no_closed hg hj₁ hj₂ h1 h2
    (hstart₁.trans hstart₂.symm) hend
  exact ⟨hlen, fun i hi => ⟨heq i hi, congrArg cov.proj (heq i hi)⟩⟩

end NonBacktrackingWalk

/-! ### Voltage covers and finite covers of girth greater than `g` -/

section VoltageCover

/-- Product of `f s * f (s + 1) * … * f (s + n - 1)` inside a monoid. -/
private def seqProd {G : Type*} [Monoid G] (f : ℕ → G) : ℕ → ℕ → G
  | _, 0 => 1
  | s, n + 1 => f s * seqProd f (s + 1) n

private theorem seqProd_succ_right {G : Type*} [Monoid G] (f : ℕ → G) (s n : ℕ) :
    seqProd f s (n + 1) = seqProd f s n * f (s + n) := by
  induction n generalizing s with
  | zero => simp [seqProd]
  | succ n ih =>
    change f s * seqProd f (s + 1) (n + 1) = (f s * seqProd f (s + 1) n) * f (s + (n + 1))
    rw [ih (s + 1), mul_assoc, show s + 1 + n = s + (n + 1) by omega]

private theorem seqProd_pi {ι : Type*} {G : ι → Type*} [∀ i, Monoid (G i)]
    (f : ℕ → ∀ i, G i) (s n : ℕ) (i : ι) :
    seqProd f s n i = seqProd (fun k => f k i) s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [seqProd, Pi.mul_apply, ih (s + 1)]

/-- Extend an injective map `f` defined on a `Finset` `dom` inside a finite type `α` to a full
permutation `Equiv.Perm α`. -/
private noncomputable def extendInjOn {α : Type*} [Fintype α] [DecidableEq α]
    (dom : Finset α) (f : α → α) (hinj : Set.InjOn f dom) :
    Equiv.Perm α := by
  let cod : Finset α := dom.image f
  have hcard_cod : cod.card = dom.card := Finset.card_image_of_injOn hinj
  have hcard_compl : Fintype.card {x : α // x ∈ domᶜ} = Fintype.card {x : α // x ∈ codᶜ} := by
    simp only [Fintype.card_coe, Finset.card_compl, hcard_cod]
  let rest : {x : α // x ∈ domᶜ} ≃ {x : α // x ∈ codᶜ} := Fintype.equivOfCardEq hcard_compl
  let toFun : α → α := fun x =>
    if hx : x ∈ dom then f x else (rest ⟨x, Finset.mem_compl.mpr hx⟩).1
  have htoFun_inj : Function.Injective toFun := by
    intro x y hxy
    dsimp only [toFun] at hxy
    split_ifs at hxy with hx hy hy
    · exact hinj hx hy hxy
    · exfalso
      have hmem_cod : f x ∈ cod := Finset.mem_image_of_mem f hx
      have hnot_cod : (rest ⟨y, Finset.mem_compl.mpr hy⟩).1 ∉ cod :=
        Finset.mem_compl.mp (rest ⟨y, Finset.mem_compl.mpr hy⟩).2
      exact hnot_cod (hxy ▸ hmem_cod)
    · exfalso
      have hmem_cod : f y ∈ cod := Finset.mem_image_of_mem f hy
      have hnot_cod : (rest ⟨x, Finset.mem_compl.mpr hx⟩).1 ∉ cod :=
        Finset.mem_compl.mp (rest ⟨x, Finset.mem_compl.mpr hx⟩).2
      exact hnot_cod (hxy ▸ hmem_cod)
    · exact congrArg Subtype.val (rest.injective (Subtype.ext hxy))
  exact Equiv.ofBijective toFun (Finite.injective_iff_bijective.mp htoFun_inj)

private theorem extendInjOn_apply {α : Type*} [Fintype α] [DecidableEq α]
    {dom : Finset α} {f : α → α} (hinj : Set.InjOn f dom) {x : α} (hx : x ∈ dom) :
    extendInjOn dom f hinj x = f x := by
  simp only [extendInjOn, Equiv.ofBijective_apply, hx, ↓reduceDIte]

/-- The **voltage graph** (regular cover / derived graph) over `H : SimpleGraph V` defined by an
antisymmetric voltage assignment `volt : V → V → Q` into a group `Q`. -/
@[expose] def voltageGraph {V Q : Type*} (H : SimpleGraph V) [Group Q]
    (volt : V → V → Q) (hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹) :
    SimpleGraph (V × Q) where
  Adj x y := H.Adj x.1 y.1 ∧ y.2 = x.2 * volt x.1 y.1
  symm := ⟨fun x y h => by
    refine ⟨h.1.symm, ?_⟩
    rw [h.2, hvolt x.1 y.1 h.1, mul_assoc, mul_inv_cancel, mul_one]⟩
  loopless := ⟨fun x h => H.loopless.irrefl x.1 h.1⟩

@[simp] theorem voltageGraph_adj {V Q : Type*} (H : SimpleGraph V) [Group Q]
    (volt : V → V → Q) (hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹)
    {x y : V × Q} :
    (voltageGraph H volt hvolt).Adj x y ↔ H.Adj x.1 y.1 ∧ y.2 = x.2 * volt x.1 y.1 :=
  Iff.rfl

/-- Canonical `SimpleGraphCover` witnessing that `voltageGraph H volt hvolt` is a finite
`|Q|`-sheeted covering of `H` via `Prod.fst`. -/
def voltageCover {V Q : Type*} (H : SimpleGraph V) [Group Q] [Fintype Q]
    (volt : V → V → Q) (hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹) :
    SimpleGraphCover (voltageGraph H volt hvolt) H (Fintype.card Q) where
  proj := Prod.fst
  hm := Fintype.card_pos_iff.mpr ⟨(1 : Q)⟩
  card_fiber_set v := by
    have hset : {p : V × Q | p.1 = v} = Set.range fun q : Q => (v, q) := by
      ext ⟨u, q⟩
      simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq]
      exact ⟨fun h => ⟨q, h.symm, rfl⟩, fun ⟨_, hu, _⟩ => hu.symm⟩
    have hinj : Function.Injective (fun q : Q => (v, q)) := fun _ _ h => (Prod.mk.inj h).2
    rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  adj_proj h := h.1
  lift_adj u' v huv := by
    refine ⟨(v, u'.2 * volt u'.1 v), ⟨rfl, huv, rfl⟩, ?_⟩
    rintro ⟨y₁, y₂⟩ ⟨hy₁, _, hy₂⟩
    subst hy₁
    exact Prod.ext rfl hy₂

@[simp] theorem voltageCover_proj {V Q : Type*} (H : SimpleGraph V) [Group Q] [Fintype Q]
    (volt : V → V → Q) (hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹) :
    (voltageCover H volt hvolt).proj = Prod.fst := by
  rfl

private theorem voltageGraph_walk_snd {V Q : Type*} {H : SimpleGraph V} [Group Q]
    {volt : V → V → Q} {hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹}
    {j : ℕ} {w' : Fin (j + 1) → V × Q}
    (hw : ∀ i : Fin j, (voltageGraph H volt hvolt).Adj (w' i.castSucc) (w' i.succ))
    (k : ℕ) (hk : k ≤ j) :
    (w' ⟨k, by omega⟩).2 = (w' 0).2 *
      seqProd (fun i => if hi : i < j then volt (w' ⟨i, by omega⟩).1 (w' ⟨i + 1, by omega⟩).1
        else 1) 0 k := by
  induction k with
  | zero => simp [seqProd]
  | succ k ih =>
    have hadj := hw ⟨k, by omega⟩
    have hstep : (w' ⟨k + 1, by omega⟩).2 =
        (w' ⟨k, by omega⟩).2 * volt (w' ⟨k, by omega⟩).1 (w' ⟨k + 1, by omega⟩).1 := hadj.2
    rw [hstep, ih (by omega), mul_assoc, seqProd_succ_right, Nat.zero_add]
    simp [show k < j by omega]

/-- A finite reduced word of length `1 ≤ len ≤ g` over the signed alphabet `E × Bool`, meaning no
two adjacent entries are the same element with opposite orientations `(e, b)` and `(e, !b)`. -/
private structure ReducedWord (E : Type*) (g : ℕ) where
  len : ℕ
  pos : 1 ≤ len
  le_g : len ≤ g
  letter : Fin len → E × Bool
  reduced : ∀ i : ℕ, (hi : i + 1 < len) →
    ¬((letter ⟨i, by omega⟩).1 = (letter ⟨i + 1, hi⟩).1 ∧
      (letter ⟨i, by omega⟩).2 = !(letter ⟨i + 1, hi⟩).2)

private def reducedWordEquiv {E : Type*} (g : ℕ) :
    ReducedWord E g ≃
      Σ k : {n : ℕ // 1 ≤ n ∧ n ≤ g},
        {f : Fin k.1 → E × Bool // ∀ i : ℕ, (hi : i + 1 < k.1) →
          ¬((f ⟨i, by omega⟩).1 = (f ⟨i + 1, hi⟩).1 ∧
            (f ⟨i, by omega⟩).2 = !(f ⟨i + 1, hi⟩).2)} where
  toFun s := ⟨⟨s.len, s.pos, s.le_g⟩, ⟨s.letter, s.reduced⟩⟩
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2, p.2.1, p.2.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨⟨_, _, _⟩, ⟨_, _⟩⟩; rfl

private instance instFiniteReducedWord {E : Type*} [Finite E] (g : ℕ) :
    Finite (ReducedWord E g) := by
  have : Finite {n : ℕ // 1 ≤ n ∧ n ≤ g} :=
    Finite.of_injective (fun n : {n : ℕ // 1 ≤ n ∧ n ≤ g} => (⟨n.1, by omega⟩ : Fin (g + 1)))
      fun a b h => Subtype.ext (congrArg Fin.val h)
  exact Finite.of_equiv _ (reducedWordEquiv g).symm

/-- For a reduced word `s` of length `k` and a generator `e : E`, build a permutation of
`Fin (k + 1)` implementing `i + 1 ↦ i` whenever `s.letter i = (e, true)` and `i ↦ i + 1` whenever
`s.letter i = (e, false)`. -/
private theorem exists_permOfReducedWord {E : Type*} {g : ℕ}
    (s : ReducedWord E g) (e : E) :
    ∃ σ : Equiv.Perm (Fin (s.len + 1)),
      (∀ i : ℕ, (hi : i < s.len) → s.letter ⟨i, hi⟩ = (e, true) →
        σ ⟨i + 1, by omega⟩ = ⟨i, by omega⟩) ∧
      (∀ i : ℕ, (hi : i < s.len) → s.letter ⟨i, hi⟩ = (e, false) →
        σ⁻¹ ⟨i + 1, by omega⟩ = ⟨i, by omega⟩) := by
  classical
  let isPos (x : Fin (s.len + 1)) : Prop :=
    ∃ hx : 0 < x.1, s.letter ⟨x.1 - 1, by omega⟩ = (e, true)
  let isNeg (x : Fin (s.len + 1)) : Prop :=
    ∃ hx : x.1 < s.len, s.letter ⟨x.1, hx⟩ = (e, false)
  let dom : Finset (Fin (s.len + 1)) := Finset.univ.filter fun x => isPos x ∨ isNeg x
  let f : Fin (s.len + 1) → Fin (s.len + 1) := fun x =>
    if h : isPos x then ⟨x.1 - 1, by omega⟩
    else if h : isNeg x then ⟨x.1 + 1, by obtain ⟨hx, _⟩ := h; omega⟩
    else x
  have hnot_both : ∀ x : Fin (s.len + 1), isPos x → isNeg x → False := by
    rintro x ⟨hxp, hp⟩ ⟨hxn, hn⟩
    refine s.reduced (x.1 - 1) (by omega) ?_
    have hidx : (⟨x.1 - 1 + 1, by omega⟩ : Fin s.len) = ⟨x.1, hxn⟩ := Fin.ext (by dsimp; omega)
    rw [hidx, hp, hn]
    exact ⟨rfl, rfl⟩
  have hinj : Set.InjOn f dom := by
    intro x hx y hy hxy
    have hxd : isPos x ∨ isNeg x := (Finset.mem_filter.mp hx).2
    have hyd : isPos y ∨ isNeg y := (Finset.mem_filter.mp hy).2
    dsimp only [f] at hxy
    rcases hxd with hxp | hxn <;> rcases hyd with hyp | hyn
    · simp only [hxp, hyp, ↓reduceDIte, Fin.mk.injEq] at hxy
      obtain ⟨hx0, _⟩ := hxp; obtain ⟨hy0, _⟩ := hyp
      exact Fin.ext (by omega)
    · have hny : ¬isPos y := fun hp => hnot_both y hp hyn
      simp only [hxp, hny, hyn, ↓reduceDIte, Fin.mk.injEq] at hxy
      obtain ⟨hx0, hp⟩ := hxp; obtain ⟨hyl, hn⟩ := hyn
      exfalso
      refine s.reduced y.1 (by omega) ?_
      have hidx : (⟨y.1 + 1, by omega⟩ : Fin s.len) = ⟨x.1 - 1, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hidx, hn, hp]
      exact ⟨rfl, rfl⟩
    · have hnx : ¬isPos x := fun hp => hnot_both x hp hxn
      simp only [hnx, hxn, hyp, ↓reduceDIte, Fin.mk.injEq] at hxy
      obtain ⟨hxl, hn⟩ := hxn; obtain ⟨hy0, hp⟩ := hyp
      exfalso
      refine s.reduced x.1 (by omega) ?_
      have hidx : (⟨x.1 + 1, by omega⟩ : Fin s.len) = ⟨y.1 - 1, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hidx, hn, hp]
      exact ⟨rfl, rfl⟩
    · have hnx : ¬isPos x := fun hp => hnot_both x hp hxn
      have hny : ¬isPos y := fun hp => hnot_both y hp hyn
      simp only [hnx, hxn, hny, hyn, ↓reduceDIte, Fin.mk.injEq] at hxy
      exact Fin.ext (by omega)
  refine ⟨extendInjOn dom f hinj, ?_, ?_⟩
  · intro i hi he
    have hpos : isPos ⟨i + 1, by omega⟩ := ⟨Nat.succ_pos i, by simpa using he⟩
    have hmem : (⟨i + 1, by omega⟩ : Fin (s.len + 1)) ∈ dom :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hpos⟩
    rw [extendInjOn_apply hinj hmem]
    simp only [f, hpos, ↓reduceDIte, Nat.add_sub_cancel]
  · intro i hi he
    refine (extendInjOn dom f hinj).inv_eq_iff_eq.mpr ?_
    symm
    have hneg : isNeg ⟨i, by omega⟩ := ⟨hi, he⟩
    have hnotpos : ¬isPos ⟨i, by omega⟩ := fun hp => hnot_both ⟨i, by omega⟩ hp hneg
    have hmem : (⟨i, by omega⟩ : Fin (s.len + 1)) ∈ dom :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hneg⟩
    rw [extendInjOn_apply hinj hmem]
    simp only [f, hnotpos, hneg, ↓reduceDIte]

private noncomputable def permOfReducedWord {E : Type*} {g : ℕ}
    (s : ReducedWord E g) (e : E) : Equiv.Perm (Fin (s.len + 1)) :=
  Classical.choose (exists_permOfReducedWord s e)

private theorem permOfReducedWord_pos {E : Type*} {g : ℕ}
    (s : ReducedWord E g) (e : E) {i : ℕ} (hi : i < s.len)
    (he : s.letter ⟨i, hi⟩ = (e, true)) :
    permOfReducedWord s e ⟨i + 1, by omega⟩ = ⟨i, by omega⟩ :=
  (Classical.choose_spec (exists_permOfReducedWord s e)).1 i hi he

private theorem permOfReducedWord_neg {E : Type*} {g : ℕ}
    (s : ReducedWord E g) (e : E) {i : ℕ} (hi : i < s.len)
    (he : s.letter ⟨i, hi⟩ = (e, false)) :
    (permOfReducedWord s e)⁻¹ ⟨i + 1, by omega⟩ = ⟨i, by omega⟩ :=
  (Classical.choose_spec (exists_permOfReducedWord s e)).2 i hi he

private theorem seqProd_perm_step {k : ℕ} (f : ℕ → Equiv.Perm (Fin (k + 1)))
    (hstep : ∀ i : ℕ, (hi : i < k) → f i ⟨i + 1, by omega⟩ = ⟨i, by omega⟩)
    (d : ℕ) (hd : d ≤ k) :
    seqProd f (k - d) d ⟨k, by omega⟩ = ⟨k - d, by omega⟩ := by
  induction d with
  | zero =>
    simp [seqProd]
  | succ d ih =>
    simp only [seqProd, Equiv.Perm.mul_apply]
    have heq : k - (d + 1) + 1 = k - d := by omega
    rw [heq, ih (by omega)]
    simpa [heq] using hstep (k - (d + 1)) (by omega)

/-- **Finite regular covers of arbitrarily high girth:** for any finite simple graph `H` on
`V : Type u` and any `g : ℕ`, there exist a finite group `Q : Type u` and a covering graph `H'`
on `V × Q` (`m = Fintype.card Q > 0`, projection `Prod.fst`) such that *every* non-backtracking
walk `w' : Fin (j + 1) → V × Q` of length `1 ≤ j ≤ g` changes the `Q`-coordinate
(`(w' 0).2 ≠ (w' (Fin.last j)).2`), and in particular is not closed (`w' 0 ≠ w' (Fin.last j)`). -/
theorem exists_voltageCover_girth_gt.{u} {V : Type u} [Finite V] (H : SimpleGraph V) (g : ℕ) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Fintype Q) (H' : SimpleGraph (V × Q))
      (cov : SimpleGraphCover H' H (Fintype.card Q)),
      cov.proj = Prod.fst ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ g →
        ∀ w' : Fin (j + 1) → V × Q, IsNBWalk H' j w' →
          (w' 0).2 ≠ (w' (Fin.last j)).2 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let ord : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let S := ReducedWord H.edgeSet g
  have : Fintype S := Fintype.ofFinite S
  let Q : Type u := ∀ s : S, Equiv.Perm (Fin (s.len + 1))
  let gen : H.edgeSet → Q := fun e s => permOfReducedWord s e
  let volt : V → V → Q := fun u v =>
    if h : H.Adj u v then
      if (ord u).1 < (ord v).1 then gen ⟨s(u, v), h⟩ else (gen ⟨s(u, v), h⟩)⁻¹
    else 1
  have hvolt : ∀ u v, H.Adj u v → volt v u = (volt u v)⁻¹ := by
    intro u v huv
    have hvu : H.Adj v u := huv.symm
    have hne : (ord u).1 ≠ (ord v).1 := fun h =>
      H.ne_of_adj huv (ord.injective (Fin.ext h))
    have hed : (⟨s(v, u), hvu⟩ : H.edgeSet) = ⟨s(u, v), huv⟩ :=
      Subtype.ext (Sym2.eq_swap)
    simp only [volt, huv, hvu, ↓reduceDIte, hed]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hnot : ¬((ord v).1 < (ord u).1) := by omega
      simp [hlt, hnot]
    · have hnot : ¬((ord u).1 < (ord v).1) := by omega
      simp [hgt, hnot]
  let H' : SimpleGraph (V × Q) := voltageGraph H volt hvolt
  let cov : SimpleGraphCover H' H (Fintype.card Q) := voltageCover H volt hvolt
  refine ⟨Q, inferInstance, inferInstance, H', cov, rfl, fun j hj1 hjg w' hw' heq_q => ?_⟩
  let w : Fin (j + 1) → V := fun i => (w' i).1
  have hw_nb : IsNBWalk H j w := hw'.map_cover cov
  let letter : Fin j → H.edgeSet × Bool := fun i =>
    (⟨s(w i.castSucc, w i.succ), hw_nb.1 i⟩, decide ((ord (w i.castSucc)).1 < (ord (w i.succ)).1))
  have hred : ∀ i : ℕ, (hi : i + 1 < j) →
      ¬((letter ⟨i, by omega⟩).1 = (letter ⟨i + 1, hi⟩).1 ∧
        (letter ⟨i, by omega⟩).2 = !(letter ⟨i + 1, hi⟩).2) := by
    intro i hi ⟨he_eq, _⟩
    have hsym : s(w ⟨i, by omega⟩, w ⟨i + 1, by omega⟩) =
        s(w ⟨i + 1, by omega⟩, w ⟨i + 2, by omega⟩) :=
      congrArg Subtype.val he_eq
    rcases Sym2.eq_iff.mp hsym with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact H.ne_of_adj (hw_nb.adj_step (i := i) (by omega)) h1
    · exact hw_nb.ne_two_step (i := i) (by omega) h1
  let s : S := ⟨j, hj1, hjg, letter, hred⟩
  let fstep : ℕ → Q := fun i =>
    if hi : i < j then volt (w ⟨i, by omega⟩) (w ⟨i + 1, by omega⟩) else 1
  have hlast_eq : (w' (Fin.last j)).2 = (w' 0).2 * seqProd fstep 0 j :=
    voltageGraph_walk_snd hw'.1 j le_rfl
  have hprod_one : seqProd fstep 0 j = 1 := by
    have : (w' 0).2 * 1 = (w' 0).2 * seqProd fstep 0 j := by
      rw [mul_one, ← hlast_eq, heq_q]
    exact (mul_left_cancel this).symm
  have hcoord_one : seqProd (fun i => fstep i s) 0 j = 1 := by
    rw [← seqProd_pi fstep 0 j s, hprod_one]
    rfl
  have hstep_s : ∀ i : ℕ, (hi : i < j) →
      (fstep i s : Equiv.Perm (Fin (j + 1))) ⟨i + 1, Nat.succ_lt_succ hi⟩ =
        ⟨i, Nat.lt_succ_of_lt hi⟩ := by
    intro i hi
    have hadj : H.Adj (w ⟨i, by omega⟩) (w ⟨i + 1, by omega⟩) := hw_nb.adj_step hi
    have hf : fstep i s = volt (w ⟨i, by omega⟩) (w ⟨i + 1, by omega⟩) s := by
      simp [fstep, hi]
    rw [hf]
    dsimp only [volt]
    simp only [hadj, ↓reduceDIte]
    by_cases hlt : (ord (w ⟨i, by omega⟩)).1 < (ord (w ⟨i + 1, by omega⟩)).1
    · simp only [hlt, ↓reduceIte]
      exact permOfReducedWord_pos s ⟨s(w ⟨i, by omega⟩, w ⟨i + 1, by omega⟩), hadj⟩ hi
        (Prod.ext rfl (decide_eq_true hlt))
    · simp only [hlt, ↓reduceIte]
      exact permOfReducedWord_neg s ⟨s(w ⟨i, by omega⟩, w ⟨i + 1, by omega⟩), hadj⟩ hi
        (Prod.ext rfl (decide_eq_false hlt))
  have hact := seqProd_perm_step (k := j) (fun i => fstep i s) hstep_s j le_rfl
  have hact' : seqProd (fun i => fstep i s) 0 j ⟨j, Nat.lt_succ_self j⟩ = ⟨0, by omega⟩ := by
    simpa [Nat.sub_self] using hact
  rw [hcoord_one, Equiv.Perm.one_apply] at hact'
  have hval : j = 0 := congrArg Fin.val hact'
  omega

/-- Every finite simple graph `H` admits a finite regular covering graph `H'` on `V × Q` with no
closed non-backtracking walk of length `1 ≤ j ≤ g`. -/
theorem exists_cover_girth_gt.{u} {V : Type u} [Finite V] (H : SimpleGraph V) (g : ℕ) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Fintype Q) (H' : SimpleGraph (V × Q))
      (cov : SimpleGraphCover H' H (Fintype.card Q)),
      cov.proj = Prod.fst ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ g →
        ∀ w' : Fin (j + 1) → V × Q, IsNBWalk H' j w' →
          w' 0 ≠ w' (Fin.last j) := by
  obtain ⟨Q, hG, hF, H', cov, hproj, hq⟩ := exists_voltageCover_girth_gt H g
  exact ⟨Q, hG, hF, H', cov, hproj, fun j hj1 hjg w' hw' heq =>
    hq j hj1 hjg w' hw' (congrArg Prod.snd heq)⟩

/-- **Connected high-girth finite cover:** every finite *connected* simple graph `H` admits a
finite *connected* `m`-sheeted covering graph `H'` with no closed non-backtracking walk of length
`1 ≤ j ≤ g`. -/
theorem exists_connected_cover_girth_gt.{u} {V : Type u} [Finite V] {H : SimpleGraph V}
    (hH : H.Connected) (g : ℕ) :
    ∃ (V' : Type u) (_ : Fintype V') (H' : SimpleGraph V') (m : ℕ)
      (_ : SimpleGraphCover H' H m),
      H'.Connected ∧
      ∀ (j : ℕ), 1 ≤ j → j ≤ g →
        ∀ w' : Fin (j + 1) → V', IsNBWalk H' j w' →
          w' 0 ≠ w' (Fin.last j) := by
  obtain ⟨Q, hG, hF, H', cov, _, hg⟩ := exists_cover_girth_gt H g
  have : Nonempty V := hH.nonempty
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  let u₀' : V × Q := (v₀, (1 : Q))
  let C := (H'.connectedComponentMk u₀').supp
  have : Finite C := inferInstance
  let fC : Fintype C := Fintype.ofFinite C
  let Hc : SimpleGraph C := H'.induce C
  let m₀ := {v' : V × Q | v' ∈ C ∧ cov.proj v' = cov.proj u₀'}.ncard
  refine ⟨C, fC, Hc, m₀, cov.restrictComponent hH u₀',
    (H'.connectedComponentMk u₀').connected_toSimpleGraph, fun j hj1 hjg w' hw' heq => ?_⟩
  exact hg j hj1 hjg (Subtype.val ∘ w') hw'.map_induce (congrArg Subtype.val heq)

end VoltageCover

end Cslib.Circuits.Frontier.CrossingCover
