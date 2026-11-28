/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polyhedra.RegularSystem
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Face graphs of convex bodies

The vertices of a convex body are joined in its face graph of level `moves`
(`Cslib.Polyhedra.faceGraph`) when they are distinct and lie on a common face of affine dimension
at most `moves`. Level `1` is the usual graph of a polytope, whose edges are its one-dimensional
faces (`Cslib.Polyhedra.faceGraph_one_adj_iff`), and higher levels allow each move to cross a
face of larger dimension. For a compact body cut out by a regular system with finitely many rows,
every face graph of level at least `1` is preconnected: from any vertex that does not maximize a
linear objective, some edge strictly improves it, as in the simplex method.

## Main definitions

* `Cslib.Polyhedra.Vertex`: the vertices (extreme points) of a set, as a type.
* `Cslib.Polyhedra.faceGraph`: vertices are adjacent when they share a face of affine dimension at
  most `moves`.

## Main results

* `Cslib.Polyhedra.faceGraph_one_adj_iff`: at level `1`, adjacency is sharing a face of affine
  dimension exactly `1`.
* `Cslib.Polyhedra.faceGraph_mono`: face graphs grow with the level.
* `Cslib.Polyhedra.exists_vertex_forall_le`: a linear functional attains its maximum over a
  nonempty compact set at a vertex.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.improving_edge`: from a vertex that is not a
  maximum of a linear objective, some edge strictly improves the objective.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.preconnected`: the face graphs of level at least `1`
  of a compact regular body are preconnected.

## Implementation notes

This is a port of
[`Graph.lean`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Graph.lean)
from the Lean formalization accompanying [OpenAI2026Hirsch] (source revision `3344da5`).
Statements are unchanged up to the following renaming (source names are in the namespace
`OAI.Geometry.Hirsch`):

| source | here |
|---|---|
| `Vertex` | `Vertex` |
| `graph` | `faceGraph` |
| `edge_iff` | `faceGraph_one_adj_iff` |
| `graph_mono` | `faceGraph_mono` |
| `vertex_max` | `exists_vertex_forall_le` |
| `System.compact_locus` | `InequalitySystem.isCompact_locus` |
| `System.Regular.improving_edge` | `InequalitySystem.IsRegular.improving_edge` |
| `System.Regular.preconnected` | `InequalitySystem.IsRegular.preconnected` |

## References

* [OpenAI2026Hirsch]
-/

@[expose] public section

noncomputable section

open Set Module

namespace Cslib.Polyhedra

variable {Space Row : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [FiniteDimensional ℝ Space]

/-- The **vertices** of a set, its extreme points, as a type. -/
abbrev Vertex (body : Set Space) := ↥(body.extremePoints ℝ)

/-- The **face graph** of level `moves` of a set: two distinct vertices are adjacent when they lie
on a common face of affine dimension at most `moves`. Level `1` is the graph (`1`-skeleton) of a
polytope. -/
def faceGraph (body : Set Space) (moves : ℕ) : SimpleGraph (Vertex body) where
  Adj first last := first ≠ last ∧ ∃ face, IsPolytopeFace body face ∧ affineDim face ≤ moves ∧
    first.val ∈ face ∧ last.val ∈ face
  symm := ⟨by rintro _ _ ⟨hn, face, hf, hd, hx, hy⟩; exact ⟨hn.symm, face, hf, hd, hy, hx⟩⟩
  loopless := ⟨fun _ hh => hh.1 rfl⟩

/-- In the face graph of level `1`, two vertices are adjacent exactly when they are distinct and
lie on a common face of affine dimension `1`, an edge. -/
theorem faceGraph_one_adj_iff {body : Set Space} {first last : Vertex body} :
    (faceGraph body 1).Adj first last ↔ first ≠ last ∧
      ∃ face, IsPolytopeFace body face ∧ affineDim face = 1 ∧ first.val ∈ face ∧
        last.val ∈ face := by
  constructor
  · rintro ⟨hn, face, hf, hd, hx, hy⟩
    have hne : affineDim face ≠ 0 := by
      intro hz
      have he := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (Submodule.finrank_eq_zero.mp hz)
      exact hn (Subtype.ext (he hx hy))
    exact ⟨hn, face, hf, by omega, hx, hy⟩
  · rintro ⟨hn, face, hf, hd, hx, hy⟩
    exact ⟨hn, face, hf, hd.le, hx, hy⟩

omit [FiniteDimensional ℝ Space] in
/-- Face graphs grow with the level. -/
theorem faceGraph_mono (body : Set Space) {small large : ℕ} (hm : small ≤ large) :
    faceGraph body small ≤ faceGraph body large := by
  rintro _ _ ⟨hn, face, hf, hd, hx, hy⟩
  exact ⟨hn, face, hf, hd.trans hm, hx, hy⟩

/-- A linear functional attains its maximum over a nonempty compact set at a vertex. -/
theorem exists_vertex_forall_le {body : Set Space} (hc : IsCompact body) (hne : body.Nonempty)
    (obj : Space →ₗ[ℝ] ℝ) :
    ∃ vertex : Vertex body, ∀ point ∈ body, obj point ≤ obj vertex.val := by
  let lin := LinearMap.toContinuousLinearMap obj
  have he := ContinuousLinearMap.toExposed.isExposed (l := lin) (A := body)
  obtain ⟨point, hp, hm⟩ := hc.exists_isMaxOn hne lin.continuous.continuousOn
  obtain ⟨best, hb⟩ := (he.isCompact hc).extremePoints_nonempty ⟨point, hp, hm⟩
  exact ⟨⟨best, he.isExtreme.extremePoints_subset_extremePoints hb⟩, hb.1.2⟩

namespace InequalitySystem

variable {sys : InequalitySystem Space Row}

/-- Every locus of a system with compact body is compact. -/
theorem isCompact_locus (hc : IsCompact sys.body) (rows : Set Row) :
    IsCompact (sys.locus rows) := by
  have he : sys.locus rows = sys.body ∩ ⋂ row ∈ rows, {p | sys.normal row p = sys.rhs row} := by
    ext point
    simp [locus, active, subset_def]
  rw [he]
  exact hc.inter_right (isClosed_iInter fun row => isClosed_iInter fun _ =>
    isClosed_eq (sys.normal row).continuous_of_finiteDimensional continuous_const)

variable [Finite Row]

/-- In a regular system with compact body, from any vertex whose objective value is exceeded at
some point of the body there is an edge to a vertex with a larger objective value. -/
theorem IsRegular.improving_edge (reg : sys.IsRegular) (hc : IsCompact sys.body)
    (obj : Space →ₗ[ℝ] ℝ) (start : Vertex sys.body) {target : Space}
    (ht : target ∈ sys.body) (hi : obj start.val < obj target) :
    ∃ finish, (faceGraph sys.body 1).Adj start finish ∧ obj start.val < obj finish.val := by
  classical
  let rows := sys.active start.val
  let := Fintype.ofFinite rows
  choose dir hd using fun pivot : rows => reg start.val start.property.1
    (fun row => if row = pivot.val then sys.normal row (target - start.val) else 0)
  have he : ∑ pivot, dir pivot = target - start.val := by
    apply sub_eq_zero.mp
    have hz : (∑ pivot, dir pivot) - (target - start.val) ∈ sys.directions rows := by
      refine sys.mem_directions.mpr fun row hr => ?_
      rw [map_sub, map_sum, Finset.sum_eq_single (⟨row, hr⟩ : rows)]
      · simp [hd _ row hr]
      · intro other _ hn
        rw [hd _ row hr, ite_eq_right (fun eqn => hn (Subtype.ext eqn.symm))]
      · simp
    rw [show sys.directions rows = ⊥ from (vertex_iff start.property.1).mp start.property] at hz
    exact hz
  have hex : ∃ pivot, 0 < obj (dir pivot) := by
    by_contra! hn
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun pivot _ => hn pivot)
    rw [← map_sum, he, map_sub] at hh
    linarith
  obtain ⟨pivot, himp⟩ := hex
  have hn : ∀ row ∈ rows, 0 ≤ sys.normal row (dir pivot) := by
    intro row hr
    rw [hd pivot row hr]
    split
    · rw [map_sub, show sys.normal row start.val = _ from hr]
      exact sub_nonneg.mpr (ht row)
    · exact le_rfl
  obtain ⟨scale, hs, hp, ha⟩ := exists_pos_step start.property.1 hn
  let keep := rows \ {pivot.val}
  have hstart : start.val ∈ sys.locus keep := ⟨start.property.1, sdiff_subset⟩
  have hpoint : start.val + scale • dir pivot ∈ sys.locus keep := by
    refine ⟨hp, ?_⟩
    rw [ha]
    intro row hr
    exact ⟨hr.1, (hd pivot row hr.1).trans (ite_eq_right hr.2)⟩
  obtain ⟨best, hb⟩ := exists_vertex_forall_le (isCompact_locus hc keep) ⟨_, hpoint⟩ obj
  have hf := sys.isPolytopeFace_locus keep
  let finish : Vertex sys.body :=
    ⟨best.val, hf.1.extremePoints_subset_extremePoints best.property⟩
  have hlt : obj start.val < obj finish.val := by
    apply lt_of_lt_of_le _ (hb _ hpoint)
    rw [map_add, map_smul, smul_eq_mul]
    exact lt_add_of_pos_right _ (mul_pos hs himp)
  have hdim : affineDim (sys.locus keep) ≤ 1 := by
    have hh := reg.dim_locus start.property.1 hstart.2
    have hk : keep.ncard + 1 = rows.ncard := ncard_sdiff_singleton_add_one pivot.property
    have hv : rows.ncard = _ := (reg.vertex_card start.property.1).mp start.property
    omega
  exact ⟨finish, ⟨fun heq => hlt.ne (congrArg (fun v => obj v.val) heq),
    _, hf, hdim, hstart, best.property.1⟩, hlt⟩

/-- For a regular system with finitely many rows and compact body, every face graph of level at
least `1` is preconnected. -/
theorem IsRegular.preconnected (reg : sys.IsRegular) (hc : IsCompact sys.body)
    {moves : ℕ} (hm : 1 ≤ moves) : (faceGraph sys.body moves).Preconnected := by
  classical
  intro start target
  let rows := sys.active target.val
  let := Fintype.ofFinite rows
  let obj := -(∑ row : rows, sys.normal row)
  let reach := {v | (faceGraph sys.body moves).Reachable start v}
  let : Finite (Vertex sys.body) := sys.finite_vertices.to_subtype
  obtain ⟨best, hb, hmax⟩ := exists_max_image reach (fun v => obj v.val) (toFinite reach)
    ⟨start, SimpleGraph.Reachable.refl _⟩
  have hle : obj target.val ≤ obj best.val := by
    by_contra! hn
    obtain ⟨next, hadj, hlt⟩ := reg.improving_edge hc obj best target.property.1 hn
    exact hlt.not_ge (hmax next (hb.trans ((faceGraph_mono _ hm) hadj).reachable))
  have hh : ∀ row : rows, sys.normal row target.val ≤ sys.normal row best.val := by
    intro row
    rw [show sys.normal row target.val = _ from row.property]
    exact best.property.1 row
  have he : ∑ row : rows, sys.normal row target.val = ∑ row : rows, sys.normal row best.val :=
    le_antisymm (Finset.sum_le_sum (fun row _ => hh row))
      (by simpa [obj, LinearMap.sum_apply] using hle)
  have hsub : rows ⊆ sys.active best.val := by
    intro row hr
    have heq := (Finset.sum_eq_sum_iff_of_le (fun row _ => hh row)).mp he
      (⟨row, hr⟩ : rows) (Finset.mem_univ _)
    exact heq.symm.trans hr
  have hd := sub_mem_directions (sys := sys) (first := target.val) Subset.rfl hsub
  rw [(vertex_iff target.property.1).mp target.property] at hd
  have heq : target = best := Subtype.ext (sub_eq_zero.mp hd)
  rwa [heq]

end InequalitySystem

end Cslib.Polyhedra
