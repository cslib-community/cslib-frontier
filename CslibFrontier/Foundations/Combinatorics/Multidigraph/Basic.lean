/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# Multidigraphs given by source and target maps

A multidigraph on vertices `V` with arcs `E` (parallel arcs and self-loops allowed) is represented
by its endpoint maps `src tgt : E → V`. Forgetting arc multiplicities yields the underlying
`Digraph V` (`Cslib.Multidigraph.toDigraph`); conversely, any simple directed graph `G : Digraph V`
embeds as the multidigraph on its arc subtype `Cslib.Multidigraph.Arc G` via
`Cslib.Multidigraph.arcSrc` and `Cslib.Multidigraph.arcTgt`, recovering `G` under `toDigraph`
(`Cslib.Multidigraph.toDigraph_arcSrc_arcTgt`).

This module also defines spanning in-arborescences `Cslib.Multidigraph.IsInArborescence` and proves
their parent-iteration characterization (`Cslib.Multidigraph.isInArborescence_iff_exists_iterate`),
from which both simple-digraph parent arborescences (`Digraph.Arborescence`) and multidigraph
matrix-tree theorems (`Multidigraph.Arborescence`) derive.

## Main definitions

* `Cslib.Multidigraph.toDigraph`: the `Digraph V` underlying `src tgt : E → V`.
* `Cslib.Multidigraph.Arc`, `Cslib.Multidigraph.arcSrc`, `Cslib.Multidigraph.arcTgt`: the
  multidigraph of arcs `{e : V × V // G.Adj e.1 e.2}` of a `Digraph V`.
* `Cslib.Multidigraph.IsInArborescence`: spanning in-arborescences rooted at `r`.

## Main results

* `Cslib.Multidigraph.toDigraph_arcSrc_arcTgt`: `toDigraph (arcSrc G) (arcTgt G) = G`.
* `Cslib.Multidigraph.reflTransGen_of_iterate_eq`,
  `Cslib.Multidigraph.exists_iterate_eq_of_reflTransGen`,
  `Cslib.Multidigraph.isInArborescence_iff_exists_iterate`: equivalence between non-root step
  reachability to `r` and iterated application of a parent map.
-/

public section

namespace Cslib.Multidigraph

variable {V E : Type*}

/-- The simple directed graph `Digraph V` underlying `src tgt : E → V`, keeping self-loops and
merging parallel arcs. -/
@[expose] def toDigraph (src tgt : E → V) : Digraph V where
  Adj u v := ∃ e, src e = u ∧ tgt e = v

@[simp]
theorem toDigraph_adj {src tgt : E → V} {u v : V} :
    (toDigraph src tgt).Adj u v ↔ ∃ e, src e = u ∧ tgt e = v :=
  Iff.rfl

/-- The arc subtype `{e : V × V // G.Adj e.1 e.2}` viewing `G : Digraph V` as a multidigraph
without parallel arcs. -/
abbrev Arc (G : Digraph V) : Type _ :=
  {e : V × V // G.Adj e.1 e.2}

/-- Source map of the canonical multidigraph of `G : Digraph V`. -/
@[expose] def arcSrc (G : Digraph V) (e : Arc G) : V :=
  e.1.1

/-- Target map of the canonical multidigraph of `G : Digraph V`. -/
@[expose] def arcTgt (G : Digraph V) (e : Arc G) : V :=
  e.1.2

@[simp]
theorem arcSrc_mk {G : Digraph V} (e : V × V) (he : G.Adj e.1 e.2) :
    arcSrc G ⟨e, he⟩ = e.1 :=
  rfl

@[simp]
theorem arcTgt_mk {G : Digraph V} (e : V × V) (he : G.Adj e.1 e.2) :
    arcTgt G ⟨e, he⟩ = e.2 :=
  rfl

theorem arc_ext_iff {G : Digraph V} {e₁ e₂ : Arc G} :
    e₁ = e₂ ↔ arcSrc G e₁ = arcSrc G e₂ ∧ arcTgt G e₁ = arcTgt G e₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Subtype.ext (Prod.ext h1 h2)⟩

/-- Forgetting multiplicities of `(arcSrc G, arcTgt G)` recovers `G`. -/
@[simp]
theorem toDigraph_arcSrc_arcTgt (G : Digraph V) : toDigraph (arcSrc G) (arcTgt G) = G := by
  ext u v
  exact ⟨fun ⟨⟨⟨a, b⟩, hab⟩, ha, hb⟩ => ha ▸ hb ▸ hab, fun huv => ⟨⟨(u, v), huv⟩, rfl, rfl⟩⟩

/-! ### Spanning in-arborescences and parent iteration -/

section Arborescence

variable (src tgt : E → V)

/-- `f` is a **spanning in-arborescence rooted at `r`** of the multidigraph `src tgt : E → V`: it
chooses an arc `f v` out of every vertex `v ≠ r`, and following the chosen arcs leads from every
vertex to `r`. -/
structure IsInArborescence (r : V) (f : {v // v ≠ r} → E) : Prop where
  /-- The arc chosen at `v` leaves `v`. -/
  src_eq : ∀ v, src (f v) = v
  /-- Following the chosen arcs leads from every vertex to the root. -/
  reachable : ∀ v, Relation.ReflTransGen (fun v w => ∃ h : v ≠ r, tgt (f ⟨v, h⟩) = w) v r

variable {src tgt}

/-- If iterating `p` reaches `r` from `v`, then `v` reaches `r` along non-root steps
`u ≠ r ∧ p u = w`. -/
theorem reflTransGen_of_iterate_eq {r : V} {p : V → V} :
    ∀ {n : ℕ} {v : V}, p^[n] v = r → Relation.ReflTransGen (fun u w => u ≠ r ∧ p u = w) v r
  | 0, v, h => by
    rw [Function.iterate_zero_apply] at h
    rw [h]
  | n + 1, v, h => by
    by_cases hv : v = r
    · rw [hv]
    · rw [Function.iterate_succ_apply] at h
      exact Relation.ReflTransGen.head ⟨hv, rfl⟩ (reflTransGen_of_iterate_eq h)

/-- If `v` reaches `r` along steps `u ≠ r ∧ p u = w`, then iterating `p` reaches `r` from `v`. -/
theorem exists_iterate_eq_of_reflTransGen {r : V} {p : V → V} {v : V}
    (h : Relation.ReflTransGen (fun u w => u ≠ r ∧ p u = w) v r) : ∃ n, p^[n] v = r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨-, rfl⟩ := hab
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

/-- Given any total parent extension `p : V → V` agreeing with `v ↦ tgt (f v)` off `r`, `f` is a
spanning in-arborescence rooted at `r` iff each chosen arc leaves its vertex and iterating `p`
reaches `r` from every vertex. -/
theorem isInArborescence_iff_exists_iterate {r : V} {f : {v // v ≠ r} → E} {p : V → V}
    (hp : ∀ v : {v // v ≠ r}, p v = tgt (f v)) :
    IsInArborescence src tgt r f ↔ (∀ v, src (f v) = v) ∧ ∀ v, ∃ n, p^[n] v = r := by
  have hrel : (fun u w => ∃ h : u ≠ r, tgt (f ⟨u, h⟩) = w) = fun u w => u ≠ r ∧ p u = w := by
    ext u w
    exact ⟨fun ⟨hu, h⟩ => ⟨hu, (hp ⟨u, hu⟩).trans h⟩,
      fun ⟨hu, h⟩ => ⟨hu, (hp ⟨u, hu⟩).symm.trans h⟩⟩
  refine ⟨fun hf => ⟨hf.src_eq, fun v => ?_⟩, fun ⟨hsrc, hit⟩ => ⟨hsrc, fun v => ?_⟩⟩
  · exact exists_iterate_eq_of_reflTransGen (hrel ▸ hf.reachable v)
  · obtain ⟨n, hn⟩ := hit v
    exact hrel.symm ▸ reflTransGen_of_iterate_eq hn

end Arborescence

end Cslib.Multidigraph
