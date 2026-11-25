/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/Branching.lean`)

public import CslibFrontier.Foundations.Combinatorics.Digraph.Arborescence
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Option
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
import Mathlib.Data.Finset.Card

/-!
# Branchings and out-arborescences

A digraph `B : Digraph V` is a **branching** (`Digraph.IsBranching`) in the sense of Edmonds
[Edmonds1967Branchings, Section 1] if every vertex has at most one incoming arc and there are no
directed cycles (so `B` is a directed forest of disjoint out-arborescences, with arcs directed away
from the roots). A **spanning out-arborescence** rooted at `r` (`Digraph.IsOutArborescence`) is
a digraph whose reversal is a spanning in-arborescence rooted at `r` (`Digraph.IsInArborescence`).

To connect optimum branchings directly with rooted minimum-cost spanning in-arborescence
algorithms, this module constructs the `Option V` super-root correspondence
(`Digraph.superRootExtend`, `Digraph.restrictOption`): adjoining a super-root `none` with an arc
`some v → none` for every vertex `v` without an incoming arc identifies the branchings `B ≤ G`
with the spanning in-arborescences `T ≤ Digraph.superRootDigraph G` rooted at `none`
(`Digraph.isBranching_iff_isInArborescence_superRootExtend`, `Digraph.restrictOption_spec`).

## Main definitions

* `Digraph.reverse`: reverse all arcs of a digraph.
* `Digraph.IsOutArborescence`, `Digraph.outParentDigraph`: spanning out-arborescences and parent
  representations with arcs `p v → v`.
* `Digraph.IsBranching`: digraphs in which each vertex has at most one incoming arc and no
  directed cycles exist.
* `Digraph.branchingDigraph`: the digraph of a parent-towards-root map `p : V → V` with fixed
  points acting as roots.
* `Digraph.superRootDigraph`, `Digraph.superRootExtend`, `Digraph.restrictOption`: the `Option V`
  super-root bijection between branchings of `G` and spanning in-arborescences rooted at `none`.

## Main results

* `Digraph.isOutArborescence_iff`, `Digraph.isOutArborescence_outParentDigraph_iff`:
  characterizations of spanning out-arborescences.
* `Digraph.isBranching_branchingDigraph_iff`, `Digraph.IsBranching.exists_branchingDigraph_eq`,
  `Digraph.IsBranching.of_rank`, `Digraph.IsBranching.exists_rank`:
  parent-map and topological-rank characterizations of branchings.
* `Digraph.isBranching_iff_isInArborescence_superRootExtend`, `Digraph.restrictOption_spec`:
  bijection with spanning in-arborescences on `Option V` rooted at `none`.
* `Digraph.IsBranching.card_arcs_le`, `Digraph.IsBranching.isOutArborescence_iff_card_arcs`:
  a finite branching on `n` vertices has at most `n - 1` arcs, with equality iff it is a spanning
  out-arborescence ([Edmonds1967Branchings, Section 1]).
* `Digraph.IsBranching.toSimpleGraph_isAcyclic`: every branching has an acyclic underlying simple
  graph.

## References

* [J. Edmonds, *Optimum Branchings*][Edmonds1967Branchings], Sections 1 and 2
-/

public section

namespace Digraph

variable {V : Type*}

/-! ### Reversal and out-arborescences -/

/-- The reversal of `G`, having an arc `u → v` iff `G` has `v → u`. -/
@[expose] def reverse (G : Digraph V) : Digraph V where
  Adj u v := G.Adj v u

instance (G : Digraph V) [DecidableRel G.Adj] : DecidableRel G.reverse.Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj v u))

@[simp]
theorem reverse_adj {G : Digraph V} {u v : V} : G.reverse.Adj u v ↔ G.Adj v u := Iff.rfl

@[simp]
theorem reverse_reverse (G : Digraph V) : G.reverse.reverse = G := rfl

theorem reverse_le_iff {G H : Digraph V} : G.reverse ≤ H.reverse ↔ G ≤ H :=
  ⟨fun h _ _ huv => h huv, fun h _ _ huv => h huv⟩

/-- `T` is a **spanning out-arborescence rooted at `r`**: an oriented spanning tree with every arc
directed away from `r` (`T.reverse.IsInArborescence r`). -/
abbrev IsOutArborescence (T : Digraph V) (r : V) : Prop :=
  T.reverse.IsInArborescence r

theorem isOutArborescence_iff {T : Digraph V} {r : V} :
    T.IsOutArborescence r ↔
      (∀ u, ¬ T.Adj u r) ∧ (∀ v, v ≠ r → ∃! u, T.Adj u v) ∧
        ∀ v, Relation.ReflTransGen T.Adj r v := by
  refine ⟨fun h => ⟨h.not_adj_root, h.existsUnique_adj, fun v => ?_⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun v => ?_⟩⟩
  · exact Relation.reflTransGen_swap.mp (h.reachable v)
  · exact Relation.reflTransGen_swap.mpr (h3 v)

/-- The out-arborescence digraph of a parent map `p` rooted at `r`: arcs `p v → v` for `v ≠ r`. -/
@[expose] def outParentDigraph (r : V) (p : V → V) : Digraph V :=
  (parentDigraph r p).reverse

@[simp]
theorem outParentDigraph_adj {r : V} {p : V → V} {u v : V} :
    (outParentDigraph r p).Adj u v ↔ v ≠ r ∧ p v = u := Iff.rfl

/-- `outParentDigraph r p` is a spanning out-arborescence rooted at `r` iff iterating `p` reaches
`r` from every vertex. -/
theorem isOutArborescence_outParentDigraph_iff {r : V} {p : V → V} :
    (outParentDigraph r p).IsOutArborescence r ↔ ∀ v, ∃ n, p^[n] v = r := by
  rw [IsOutArborescence, outParentDigraph, reverse_reverse]
  exact isInArborescence_parentDigraph_iff

/-- Every spanning out-arborescence rooted at `r` is `outParentDigraph r p` for some parent map `p`
with `p r = r`. -/
theorem IsOutArborescence.exists_outParentDigraph_eq {T : Digraph V} {r : V}
    (hT : T.IsOutArborescence r) : ∃ p : V → V, p r = r ∧ outParentDigraph r p = T := by
  obtain ⟨p, hpr, hp⟩ := IsInArborescence.exists_parentDigraph_eq hT
  exact ⟨p, hpr, by rw [outParentDigraph, hp, reverse_reverse]⟩

/-! ### Branchings -/

/-- A digraph `B` is a **branching** [Edmonds1967Branchings, Section 1] if each vertex has at most
one incoming arc and `B` has no directed cycles. -/
structure IsBranching (B : Digraph V) : Prop where
  /-- Each vertex has at most one incoming arc. -/
  in_unique : ∀ ⦃u₁ u₂ v : V⦄, B.Adj u₁ v → B.Adj u₂ v → u₁ = u₂
  /-- `B` has no directed cycles (including self-loops). -/
  acyclic : ∀ ⦃v : V⦄, ¬ Relation.TransGen B.Adj v v

theorem IsBranching.loopless {B : Digraph V} (hB : B.IsBranching) (v : V) : ¬ B.Adj v v :=
  fun h => hB.acyclic (Relation.TransGen.single h)

theorem IsBranching.no_two_cycle {B : Digraph V} (hB : B.IsBranching) {u v : V}
    (huv : B.Adj u v) : ¬ B.Adj v u :=
  fun hvu => hB.acyclic (Relation.TransGen.tail (Relation.TransGen.single huv) hvu)

theorem IsBranching.anti {B B' : Digraph V} (hle : B' ≤ B) (hB : B.IsBranching) :
    B'.IsBranching where
  in_unique _ _ _ h1 h2 := hB.in_unique (hle h1) (hle h2)
  acyclic _ hc := hB.acyclic (Relation.TransGen.mono (fun _ _ h => hle h) _ _ hc)

theorem isBranching_bot (V : Type*) : (⊥ : Digraph V).IsBranching where
  in_unique _ _ _ h := by simp at h
  acyclic _ h := by cases h <;> simp_all

/-- A digraph whose arcs strictly increase some `ℕ`-valued rank and give each vertex at most one
incoming arc is a branching. -/
theorem IsBranching.of_rank {B : Digraph V} {rk : V → ℕ}
    (hrank : ∀ ⦃u w : V⦄, B.Adj u w → rk u < rk w)
    (hin : ∀ ⦃u₁ u₂ w : V⦄, B.Adj u₁ w → B.Adj u₂ w → u₁ = u₂) :
    B.IsBranching where
  in_unique := hin
  acyclic _ hc := by
    have hlt : ∀ {x y : V}, Relation.TransGen B.Adj x y → rk x < rk y := by
      intro x y hxy
      induction hxy with
      | single h => exact hrank h
      | tail _ h ih => exact ih.trans (hrank h)
    exact Nat.lt_irrefl _ (hlt hc)

/-- Helper: following a walk in `outParentDigraph` backward tracks iterates of `p`. -/
private theorem transGen_outParentDigraph_iterate {r : V} {p : V → V} {x y : V}
    (hxy : Relation.TransGen (outParentDigraph r p).Adj x y) :
    ∃ k, 0 < k ∧ p^[k] y = x := by
  induction hxy with
  | single h => exact ⟨1, Nat.zero_lt_one, by simpa using h.2⟩
  | tail _ h ih =>
    obtain ⟨k, hk, hpk⟩ := ih
    exact ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply, h.2, hpk]⟩

/-- Helper: a periodic point of `p` from which iterating `p` reaches a fixed point `r` is `r`. -/
private theorem eq_of_iterate_periodic_of_fixed {α : Type*} {p : α → α} {r x : α}
    (hpr : p r = r) {k n : ℕ} (hk : 0 < k) (hpk : p^[k] x = x) (hn : p^[n] x = r) : x = r := by
  have hcyc : p^[k * n] x = x := (show Function.IsPeriodicPt p k x from hpk).mul_const n
  rw [← hcyc, ← Nat.sub_add_cancel (Nat.le_mul_of_pos_left n hk), Function.iterate_add_apply, hn,
    Function.iterate_fixed hpr]

/-- A spanning out-arborescence is a branching. -/
theorem IsBranching.of_isOutArborescence {T : Digraph V} {r : V} (hT : T.IsOutArborescence r) :
    T.IsBranching := by
  obtain ⟨p, hpr, rfl⟩ := hT.exists_outParentDigraph_eq
  refine ⟨fun _ _ _ h1 h2 => h1.2.symm.trans h2.2, fun v hc => ?_⟩
  obtain ⟨k, hk, hpk⟩ := transGen_outParentDigraph_iterate hc
  obtain ⟨n, hn⟩ := (isOutArborescence_outParentDigraph_iff.mp hT) v
  obtain ⟨-, -, hne, -⟩ := Relation.TransGen.tail'_iff.mp hc
  exact hne (eq_of_iterate_periodic_of_fixed hpr hk hpk hn)

/-! ### Parent-map representation of branchings -/

/-- The digraph of a parent-towards-root map `p`: an arc `p v → v` whenever `p v ≠ v`. Vertices
with `p v = v` are the roots of the branching's component out-arborescences. -/
@[expose] def branchingDigraph (p : V → V) : Digraph V where
  Adj u v := p v ≠ v ∧ p v = u

instance [DecidableEq V] (p : V → V) : DecidableRel (branchingDigraph p).Adj :=
  fun u v => inferInstanceAs (Decidable (p v ≠ v ∧ p v = u))

@[simp]
theorem branchingDigraph_adj {p : V → V} {u v : V} :
    (branchingDigraph p).Adj u v ↔ p v ≠ v ∧ p v = u := Iff.rfl

private theorem transGen_branchingDigraph_iterate {p : V → V} {x y : V}
    (hxy : Relation.TransGen (branchingDigraph p).Adj x y) :
    ∃ k, 0 < k ∧ p^[k] y = x ∧ ∀ i < k, p (p^[i] y) ≠ p^[i] y := by
  induction hxy with
  | single h =>
    exact ⟨1, Nat.zero_lt_one, by simpa using h.2, fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using h.1⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk, hpk, hne⟩ := ih
    refine ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply, hbc.2, hpk], fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using hbc.1
    · simpa only [Function.iterate_succ_apply, hbc.2] using hne i (Nat.succ_lt_succ_iff.mp hi)

private theorem reflTransGen_branchingDigraph_iterate (p : V → V) (v : V) (m : ℕ) :
    Relation.ReflTransGen (branchingDigraph p).Adj (p^[m] v) v := by
  induction m with
  | zero => exact .refl
  | succ m ih =>
    by_cases hpm : p (p^[m] v) = p^[m] v
    · rwa [Function.iterate_succ_apply', hpm]
    · exact .head ⟨hpm, (Function.iterate_succ_apply' ..).symm⟩ ih

/-- `branchingDigraph p` is a branching when iterating `p` from every vertex reaches a fixed point
(root). On finite vertex types the converse also holds. -/
theorem isBranching_branchingDigraph_of_reach_fixed {p : V → V}
    (hfix : ∀ v, ∃ n, p (p^[n] v) = p^[n] v) : (branchingDigraph p).IsBranching := by
  refine ⟨fun _ _ _ h1 h2 => h1.2.symm.trans h2.2, fun v hc => ?_⟩
  obtain ⟨k, hk, hpk, hne⟩ := transGen_branchingDigraph_iterate hc
  obtain ⟨n, hn⟩ := hfix v
  exact hne 0 hk (by simpa [← eq_of_iterate_periodic_of_fixed hn hk hpk rfl] using hn)

/-- On a finite vertex type, `branchingDigraph p` is a branching iff iterating `p` reaches a fixed
point from every vertex. -/
theorem isBranching_branchingDigraph_iff [Finite V] {p : V → V} :
    (branchingDigraph p).IsBranching ↔ ∀ v, ∃ n, p (p^[n] v) = p^[n] v := by
  refine ⟨fun hB v => ?_, isBranching_branchingDigraph_of_reach_fixed⟩
  have := Fintype.ofFinite V
  obtain ⟨n, hn⟩ := Cslib.FunctionalGraph.exists_iterate_mem_periodicPts p v
  refine ⟨n, ?_⟩
  set k := Function.minimalPeriod p (p^[n] v) with hk
  have hkpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts hn
  have hper : p^[k] (p^[n] v) = p^[n] v := Function.isPeriodicPt_minimalPeriod p _
  by_contra hne
  have hall : ∀ i < k, p (p^[i] (p^[n] v)) ≠ p^[i] (p^[n] v) := by
    intro i hi heq
    have hloop : p^[i] (p^[n] v) = p^[n] v := (Function.iterate_fixed heq (k - i)).symm.trans
      (by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi.le, hper])
    exact hne (hloop ▸ heq)
  have htg : ∀ m, 0 < m → m ≤ k →
      Relation.TransGen (branchingDigraph p).Adj (p^[m] (p^[n] v)) (p^[n] v) := by
    intro m hm hmk
    induction m, hm using Nat.le_induction with
    | base => exact .single ⟨hall 0 hkpos, rfl⟩
    | succ m hm ih =>
      exact .head ⟨hall m hmk, by rw [Function.iterate_succ_apply']⟩ (ih (by omega))
  have hcycle := htg k hkpos le_rfl
  rw [hper] at hcycle
  exact hB.acyclic hcycle

/-- Every branching is `branchingDigraph p` for a parent-towards-root map `p` fixing every vertex
with no incoming arc. -/
theorem IsBranching.exists_branchingDigraph_eq {B : Digraph V} (hB : B.IsBranching) :
    ∃ p : V → V, (∀ v, p v = v ↔ ¬ ∃ u, B.Adj u v) ∧ branchingDigraph p = B := by
  classical
  let p : V → V := fun v => if h : ∃ u, B.Adj u v then h.choose else v
  have hspec {v : V} (hv : ∃ u, B.Adj u v) : B.Adj (p v) v := by
    simpa only [p, dite_eq_left hv] using hv.choose_spec
  refine ⟨p, fun v => ⟨fun hp hv => hB.loopless v (by simpa only [hp] using hspec hv),
    fun hno => by simp [p, dite_eq_right hno]⟩, ?_⟩
  ext u v
  refine ⟨fun ⟨hne, hpu⟩ => ?_, fun huv => ?_⟩
  · by_cases hv : ∃ w, B.Adj w v
    · exact hpu ▸ hspec hv
    · exact absurd (dite_eq_right hv) hne
  · have hpeq : p v = u := hB.in_unique (hspec ⟨u, huv⟩) huv
    exact ⟨fun h => hB.loopless v (by rwa [← hpeq, h] at huv), hpeq⟩

/-- Every branching on a finite vertex type admits a strict root-distance ranking `rk : V → ℕ`
that increases along every arc. -/
theorem IsBranching.exists_rank [Finite V] {B : Digraph V} (hB : B.IsBranching) :
    ∃ rk : V → ℕ, ∀ ⦃u w : V⦄, B.Adj u w → rk u < rk w := by
  classical
  obtain ⟨p, _, rfl⟩ := hB.exists_branchingDigraph_eq
  have hfix := isBranching_branchingDigraph_iff.mp hB
  refine ⟨fun v => Nat.find (hfix v), fun u w ⟨hne, hpu⟩ => ?_⟩
  subst hpu
  rcases hk : Nat.find (hfix w) with _ | m
  · exact absurd (by simpa [hk] using Nat.find_spec (hfix w)) hne
  · have hm : p (p^[m] (p w)) = p^[m] (p w) := by
      simpa only [hk, Function.iterate_succ_apply] using Nat.find_spec (hfix w)
    dsimp only
    rw [hk]
    exact Nat.lt_succ_of_le (Nat.find_min' (hfix (p w)) hm)

/-! ### Super-root bijection on `Option V` -/

/-- The super-root augmentation of `G` on `Option V`: real arcs of `G` are reversed (`some v →
some u` iff `G.Adj u v`), and every vertex `some v` also has a rootward arc to `none`. -/
@[expose] def superRootDigraph (G : Digraph V) : Digraph (Option V) where
  Adj x y := match x, y with
    | some v, some u => G.Adj u v
    | some _, none => True
    | none, _ => False

instance (G : Digraph V) [DecidableRel G.Adj] : DecidableRel (superRootDigraph G).Adj :=
  fun x y => by
    cases x <;> cases y
    · exact inferInstanceAs (Decidable False)
    · exact inferInstanceAs (Decidable False)
    · exact inferInstanceAs (Decidable True)
    · exact inferInstanceAs (Decidable (G.Adj _ _))

@[simp]
theorem superRootDigraph_some_some (G : Digraph V) (u v : V) :
    (superRootDigraph G).Adj (some v) (some u) ↔ G.Adj u v := Iff.rfl

@[simp]
theorem superRootDigraph_some_none (G : Digraph V) (v : V) :
    (superRootDigraph G).Adj (some v) none := trivial

@[simp]
theorem superRootDigraph_none (G : Digraph V) (y : Option V) :
    ¬ (superRootDigraph G).Adj none y := by
  cases y <;> simp [superRootDigraph]

/-- Extend a subdigraph `B : Digraph V` to `Option V` by sending every vertex without an incoming
arc in `B` to `none`, and reversing existing arcs of `B`. -/
@[expose] def superRootExtend (B : Digraph V) : Digraph (Option V) where
  Adj x y := match x, y with
    | some v, some u => B.Adj u v
    | some v, none => ¬ ∃ u, B.Adj u v
    | none, _ => False

@[simp]
theorem superRootExtend_some_some (B : Digraph V) (u v : V) :
    (superRootExtend B).Adj (some v) (some u) ↔ B.Adj u v := Iff.rfl

@[simp]
theorem superRootExtend_some_none (B : Digraph V) (v : V) :
    (superRootExtend B).Adj (some v) none ↔ ¬ ∃ u, B.Adj u v := Iff.rfl

@[simp]
theorem superRootExtend_none (B : Digraph V) (y : Option V) :
    ¬ (superRootExtend B).Adj none y := by
  cases y <;> simp [superRootExtend]

theorem superRootExtend_le_superRootDigraph {B G : Digraph V} (hBG : B ≤ G) :
    superRootExtend B ≤ superRootDigraph G := by
  intro x y hxy
  cases x <;> cases y <;> first | exact False.elim hxy | exact trivial | exact hBG hxy

/-- Restrict an `Option V` digraph back to `V` by forgetting `none` and reversing real arcs. -/
@[expose] def restrictOption (T : Digraph (Option V)) : Digraph V where
  Adj u v := T.Adj (some v) (some u)

instance (T : Digraph (Option V)) [DecidableRel T.Adj] :
    DecidableRel (restrictOption T).Adj :=
  fun u v => inferInstanceAs (Decidable (T.Adj (some v) (some u)))

@[simp]
theorem restrictOption_adj (T : Digraph (Option V)) (u v : V) :
    (restrictOption T).Adj u v ↔ T.Adj (some v) (some u) := Iff.rfl

@[simp]
theorem restrictOption_superRootExtend (B : Digraph V) :
    restrictOption (superRootExtend B) = B := rfl

private theorem reflTransGen_superRootExtend_some {B : Digraph V} {u v : V}
    (h : Relation.ReflTransGen B.Adj u v) :
    Relation.ReflTransGen (superRootExtend B).Adj (some v) (some u) := by
  exact Relation.reflTransGen_swap.mpr (h.lift some fun _ _ hab => hab)

/-- Helper: if `T` is an in-arborescence rooted at `none`, its restriction to `V` is acyclic. -/
private theorem transGen_superRoot_of_restrict {T : Digraph (Option V)} {x y : V}
    (h : Relation.TransGen (restrictOption T).Adj x y) :
    Relation.TransGen T.Adj (some y) (some x) := by
  exact Relation.transGen_swap.mpr (h.lift some fun _ _ hab => hab)

/-- For a finite vertex type, a digraph `B` is a branching iff its super-root extension on
`Option V` is a spanning in-arborescence rooted at `none`. -/
theorem isBranching_iff_isInArborescence_superRootExtend [Finite V] {B : Digraph V} :
    B.IsBranching ↔ (superRootExtend B).IsInArborescence none := by
  classical
  constructor
  · intro hB
    obtain ⟨p, hproot, rfl⟩ := hB.exists_branchingDigraph_eq
    have hpfix : ∀ v, ∃ n, p (p^[n] v) = p^[n] v :=
      isBranching_branchingDigraph_iff.mp hB
    refine ⟨fun _ h => superRootExtend_none _ _ h, ?_, ?_⟩
    · rintro (_ | v) hne
      · exact absurd rfl hne
      · by_cases hv : ∃ u, (branchingDigraph p).Adj u v
        · have ⟨u, hu⟩ := hv
          refine ⟨some u, hu, ?_⟩
          rintro (_ | w) hw
          · exact absurd hv hw
          · exact congrArg some (hB.in_unique hw hu)
        · refine ⟨none, hv, ?_⟩
          rintro (_ | w) hw
          · rfl
          · exact absurd ⟨w, hw⟩ hv
    · rintro (_ | v)
      · exact Relation.ReflTransGen.refl
      · obtain ⟨n, hn⟩ := hpfix v
        exact (reflTransGen_superRootExtend_some (reflTransGen_branchingDigraph_iterate p v n)).tail
          ((superRootExtend_some_none _ _).mpr ((hproot _).mp hn))
  · intro hT
    refine ⟨fun u₁ u₂ v h1 h2 => ?_, fun v hc => ?_⟩
    · exact Option.some.inj ((hT.existsUnique_adj (some v) (Option.some_ne_none v)).unique h1 h2)
    · have hc' : Relation.TransGen (superRootExtend B).Adj (some v) (some v) :=
        transGen_superRoot_of_restrict hc
      obtain ⟨p, hpr, hp⟩ := hT.exists_parentDigraph_eq
      rw [← hp] at hc'
      have hreach := (isInArborescence_parentDigraph_iff.mp (hp ▸ hT)) (some v)
      have hstep : ∀ {x y : Option V}, Relation.TransGen (parentDigraph none p).Adj x y →
          ∃ k, 0 < k ∧ p^[k] x = y := by
        intro x y hxy
        induction hxy with
        | single h => exact ⟨1, Nat.zero_lt_one, by simpa using h.2⟩
        | tail _ h ih =>
          obtain ⟨k, hk, hpk⟩ := ih
          exact ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply', hpk, h.2]⟩
      obtain ⟨k, hk, hpk⟩ := hstep hc'
      obtain ⟨n, hn⟩ := hreach
      exact Option.some_ne_none v (eq_of_iterate_periodic_of_fixed hpr hk hpk hn)

/-- Every spanning in-arborescence `T` on `Option V` rooted at `none` restricts to a branching on
`V` whose super-root extension equals `T`, and `T ≤ superRootDigraph G` iff the branching lies in
`G`. -/
theorem restrictOption_spec [Finite V] {T : Digraph (Option V)} (hT : T.IsInArborescence none) :
    (restrictOption T).IsBranching ∧ superRootExtend (restrictOption T) = T ∧
      ∀ G : Digraph V, T ≤ superRootDigraph G → restrictOption T ≤ G := by
  have hext : superRootExtend (restrictOption T) = T := by
    ext x y
    rcases x with _ | v <;> rcases y with _ | u
    · simp [hT.not_adj_root]
    · simp [hT.not_adj_root]
    · have hu := hT.existsUnique_adj (some v) (Option.some_ne_none v)
      refine ⟨fun hnone => ?_, fun hvn ⟨u, hvu⟩ => Option.some_ne_none u (hu.unique hvu hvn)⟩
      obtain ⟨_ | u, hy, -⟩ := hu
      exacts [hy, absurd ⟨u, hy⟩ hnone]
    · simp
  exact ⟨isBranching_iff_isInArborescence_superRootExtend.mpr (hext ▸ hT), hext,
    fun G hTG u v huv => hTG huv⟩

/-! ### Arc counts, spanning out-arborescences, and undirected forests -/

/-- A finite nonempty branching has at least one root (a vertex with no incoming arc). -/
theorem IsBranching.exists_not_adj_into [Finite V] [Nonempty V] {B : Digraph V}
    (hB : B.IsBranching) :
    ∃ r : V, ∀ u : V, ¬ B.Adj u r := by
  obtain ⟨p, hp, rfl⟩ := hB.exists_branchingDigraph_eq
  obtain ⟨n, hn⟩ := isBranching_branchingDigraph_iff.mp hB (Classical.arbitrary V)
  refine ⟨p^[n] (Classical.arbitrary V), fun u hu => ?_⟩
  rw [hp] at hn
  exact absurd ⟨u, hu⟩ hn

section ArcCount

variable [Fintype V]

/-- Every vertex without an incoming arc in a branching is a root; the number of arcs plus the
number of roots equals the number of vertices. -/
theorem IsBranching.card_arcs_add_card_roots {B : Digraph V} [DecidableRel B.Adj]
    (hB : B.IsBranching) :
    (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card +
        (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card =
      Fintype.card V := by
  classical
  let arcs := Finset.univ.filter fun e : V × V => B.Adj e.1 e.2
  let nonroots := Finset.univ.filter fun v : V => ∃ u, B.Adj u v
  let roots := Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v
  have hbij : arcs.card = nonroots.card := by
    refine Finset.card_bij (fun e _ => e.2)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1, (Finset.mem_filter.mp he).2⟩)
      (fun _ he₁ _ he₂ heq => Prod.ext
        (hB.in_unique (Finset.mem_filter.mp he₁).2 (heq ▸ (Finset.mem_filter.mp he₂).2)) heq)
      fun v hv => ?_
    obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hv).2
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
  have hdisj : Disjoint nonroots roots :=
    Finset.disjoint_filter.mpr fun _ _ h h' => h' h
  have hunion : nonroots ∪ roots = Finset.univ := by
    ext v
    simpa [nonroots, roots] using Classical.em (∃ u, B.Adj u v)
  have hpart : nonroots.card + roots.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  simpa [arcs, roots] using (congrArg (· + roots.card) hbij).trans hpart

/-- **Edmonds (1967, Section 1):** No branching on `n` vertices has more than `n - 1` arcs. -/
theorem IsBranching.card_arcs_le {B : Digraph V} [DecidableRel B.Adj] (hB : B.IsBranching) :
    (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card ≤ Fintype.card V - 1 := by
  rcases isEmpty_or_nonempty V with hempty | hne
  · simp [Fintype.card_eq_zero]
  · obtain ⟨r, hr⟩ := hB.exists_not_adj_into
    have hpos : 0 < (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card :=
      Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ⟨u, hu⟩ => hr u hu⟩⟩
    have hsum := hB.card_arcs_add_card_roots
    omega

/-- **Edmonds (1967, Section 1):** A branching on `n ≥ 1` vertices is a spanning out-arborescence
iff it has `n - 1` arcs. -/
theorem IsBranching.isOutArborescence_iff_card_arcs [Nonempty V] {B : Digraph V}
    [DecidableRel B.Adj] (hB : B.IsBranching) :
    (∃ r : V, B.IsOutArborescence r) ↔
      (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card = Fintype.card V - 1 := by
  have hsum := hB.card_arcs_add_card_roots
  constructor
  · rintro ⟨r, hT⟩
    have huniv : (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v) = {r} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine ⟨fun hv => by_contra fun hvr => ?_, by rintro rfl ⟨u, hu⟩; exact hT.not_adj_root u hu⟩
      obtain ⟨u, hu, -⟩ := (isOutArborescence_iff.mp hT).2.1 v hvr
      exact hv ⟨u, hu⟩
    rw [huniv, Finset.card_singleton] at hsum
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    omega
  · intro hcard
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hroots : (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card = 1 := by omega
    obtain ⟨r, hrset⟩ := Finset.card_eq_one.mp hroots
    have hmem : ∀ v, (¬ ∃ u, B.Adj u v) ↔ v = r := fun v => by
      simpa using Finset.ext_iff.mp hrset v
    refine ⟨r, isOutArborescence_iff.mpr ⟨fun u hu => (hmem r).mpr rfl ⟨u, hu⟩, ?_, ?_⟩⟩
    · intro v hvr
      obtain ⟨u, hu⟩ : ∃ u, B.Adj u v := by_contra fun hv => hvr ((hmem v).mp hv)
      exact ⟨u, hu, fun w hw => hB.in_unique hw hu⟩
    · obtain ⟨p, hp, hpeq⟩ := hB.exists_branchingDigraph_eq
      subst hpeq
      intro v
      obtain ⟨n, hn⟩ := isBranching_branchingDigraph_iff.mp hB v
      have hfix : p^[n] v = r := (hmem _).mp ((hp _).mp hn)
      simpa [hfix] using reflTransGen_branchingDigraph_iterate p v n

end ArcCount

/-! ### Acyclicity of the underlying undirected simple graph -/

/-- Along any non-nil trail of `SimpleGraph.fromRel B.Adj` starting with a forward arc `u → x`,
every edge in a branching points forward, giving a directed walk `TransGen B.Adj u v`. -/
private theorem transGen_of_walk_fromRel_isTrail {B : Digraph V} (hB : B.IsBranching) :
    ∀ {u x v : V} (hx : (SimpleGraph.fromRel B.Adj).Adj u x)
      (p' : (SimpleGraph.fromRel B.Adj).Walk x v),
      (SimpleGraph.Walk.cons hx p').IsTrail → B.Adj u x → Relation.TransGen B.Adj u v
  | u, x, _, _, .nil, _, hux => Relation.TransGen.single hux
  | u, x, _, hx, @SimpleGraph.Walk.cons _ _ _ y z hyz q, htr, hux => by
    have hne : u ≠ y := fun huy =>
      (List.nodup_cons.mp htr.edges_nodup).1 (List.mem_cons.mpr (.inl (huy ▸ Sym2.eq_swap)))
    have hxy : B.Adj x y := ((SimpleGraph.fromRel_adj B.Adj x y).mp hyz).2.resolve_right
      fun h => hne (hB.in_unique hux h)
    exact Relation.TransGen.head hux
      (transGen_of_walk_fromRel_isTrail hB hyz q htr.of_cons hxy)

/-- **Edmonds (1967, Section 1):** Every branching has an acyclic underlying undirected simple
graph (forest). -/
theorem IsBranching.toSimpleGraph_isAcyclic {B : Digraph V} (hB : B.IsBranching) :
    (SimpleGraph.fromRel B.Adj).IsAcyclic := by
  intro v c hc
  cases c with
  | nil => exact absurd hc SimpleGraph.Walk.not_isCycle_nil
  | @cons _ u _ huv p =>
    have htr : (SimpleGraph.Walk.cons huv p).IsTrail := hc.isCircuit.isTrail
    rcases (SimpleGraph.fromRel_adj B.Adj v u).mp huv |>.2 with hvu | huv'
    · exact hB.acyclic (transGen_of_walk_fromRel_isTrail hB huv p htr hvu)
    · have hc_rev : (SimpleGraph.Walk.cons huv p).reverse.IsCycle := hc.reverse
      have hlen : 3 ≤ (SimpleGraph.Walk.cons huv p).length := hc.three_le_length
      cases hrev : (SimpleGraph.Walk.cons huv p).reverse with
      | nil => exact absurd (hrev ▸ hc_rev) SimpleGraph.Walk.not_isCycle_nil
      | @cons _ w _ hwv q =>
        have htr_rev : (SimpleGraph.Walk.cons hwv q).IsTrail := hrev ▸ hc_rev.isCircuit.isTrail
        have hnd : (s(v, u) :: p.edges).Nodup := by simpa using htr.edges_nodup
        have hrev_edges : (s(v, w) :: q.edges) = p.edges.reverse ++ [s(v, u)] := by
          have := congrArg SimpleGraph.Walk.edges hrev
          simpa [SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using this.symm
        have hmem_edge : s(v, w) ∈ p.edges := by
          rcases hpe : p.edges.reverse with _ | ⟨e, es⟩
          · have hlen0 := congrArg List.length hpe
            simp only [List.length_reverse, SimpleGraph.Walk.length_edges, List.length_nil] at hlen0
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega
          · rw [hpe, List.cons_append, List.cons.injEq] at hrev_edges
            exact List.mem_reverse.mp (hpe ▸ hrev_edges.1 ▸ List.mem_cons_self)
        have hwu_ne : w ≠ u := fun hwu => (List.nodup_cons.mp hnd).1 (hwu ▸ hmem_edge)
        have hvw : B.Adj v w := ((SimpleGraph.fromRel_adj B.Adj v w).mp hwv).2.resolve_right
          fun h => hwu_ne (hB.in_unique h huv')
        exact hB.acyclic (transGen_of_walk_fromRel_isTrail hB hwv q htr_rev hvw)

end Digraph
