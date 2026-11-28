/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polyhedra.InequalitySystem

/-!
# Regular systems of linear inequalities

A system of linear inequalities is regular (`Cslib.Polyhedra.InequalitySystem.IsRegular`) when,
at every point of its body, the normals of the active rows can be given arbitrary values by a
single direction: they are linearly independent, and in particular no row is active without being
needed. For a regular system with finitely many rows on a finite-dimensional space, faces are
counted by active rows: the locus of `k` rows active at a common point has affine dimension
`dim - k`, the facets are exactly the walls of the rows that are active somewhere, and the body
is simple.

## Main definitions

* `Cslib.Polyhedra.InequalitySystem.IsRegular`: the active normals at every point of the body are
  linearly independent.
* `Cslib.Polyhedra.InequalitySystem.used`: the rows active at some point of the body.
* `Cslib.Polyhedra.InequalitySystem.wall`: the locus of a single row.

## Main results

* `Cslib.Polyhedra.InequalitySystem.finite_vertices`,
  `Cslib.Polyhedra.InequalitySystem.finite_facets`: finitely many rows give finitely many vertices
  and facets.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.dim_locus`: a set of rows active at a common point
  has a locus of affine dimension `finrank - ncard`.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.vertex_card`: the vertices are the points with
  `finrank` active rows.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.facets_eq`,
  `Cslib.Polyhedra.InequalitySystem.IsRegular.ncard_facets`: the facets are the walls of the used
  rows, one for each.
* `Cslib.Polyhedra.InequalitySystem.IsRegular.isSimple`: the body of a regular system is simple.

## Implementation notes

This is a port of
[`Regular.lean`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Regular.lean)
from the Lean formalization accompanying [OpenAI2026Hirsch] (source revision `3344da5`).
Statements are unchanged up to the following renaming (source names are in the namespace
`OAI.Geometry.Hirsch.System`):

| source | here |
|---|---|
| `Regular` | `IsRegular` |
| `Regular.facet_count` | `IsRegular.ncard_facets` |
| `Regular.simple` | `IsRegular.isSimple` |

All other declarations keep their source names under `Cslib.Polyhedra.InequalitySystem`, with
`dim` read as `affineDim`.

## References

* [OpenAI2026Hirsch]
-/

@[expose] public section

noncomputable section

open Set Module

namespace Cslib.Polyhedra.InequalitySystem

variable {Space Row : Type*} [AddCommGroup Space] [Module ℝ Space]
variable (sys : InequalitySystem Space Row)

/-- The linear map recording the values of the normals of a set of rows. -/
def evaluation (rows : Set Row) : Space →ₗ[ℝ] (rows → ℝ) :=
  LinearMap.pi fun row => sys.normal row

/-- The kernel of `evaluation rows` is `directions rows`. -/
theorem ker_evaluation (rows : Set Row) :
    (sys.evaluation rows).ker = sys.directions rows := by
  ext dir
  simp [evaluation, mem_directions, funext_iff]

/-- A system is **regular** when at every point of its body some direction gives the normals of
the active rows any prescribed values; equivalently, the active normals at every point are
linearly independent. -/
def IsRegular : Prop :=
  ∀ point ∈ sys.body, ∀ values : Row → ℝ,
    ∃ dir, ∀ row ∈ sys.active point, sys.normal row dir = values row

/-- The rows **used** by a system: those active at some point of its body. -/
def used : Set Row := {row | ∃ point ∈ sys.body, row ∈ sys.active point}

/-- The **wall** of a row: the points of the body where it is tight. -/
def wall (row : Row) : Set Space := sys.locus {row}

variable {sys} {point : Space} {rows : Set Row}

/-- In a regular system, the normals of rows active at a common point can take any values. -/
theorem IsRegular.surjective (reg : sys.IsRegular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) : Function.Surjective (sys.evaluation rows) := by
  classical
  intro values
  obtain ⟨dir, hd⟩ := reg point hp fun row => if hh : row ∈ rows then values ⟨row, hh⟩ else 0
  refine ⟨dir, funext fun row => ?_⟩
  simpa [evaluation] using hd row (hr row.property)

variable [Finite Row]

/-- A system with finitely many rows has finitely many vertices. -/
theorem finite_vertices (sys : InequalitySystem Space Row) :
    (sys.body.extremePoints ℝ).Finite := by
  apply (Set.toFinite (sys.active '' sys.body.extremePoints ℝ)).of_finite_image
  intro first hf last hl he
  have hd := sub_mem_directions (sys := sys) (first := first) Subset.rfl he.subset
  rw [(vertex_iff hf.1).mp hf] at hd
  exact sub_eq_zero.mp hd

/-- A system with finitely many rows has finitely many facets. -/
theorem finite_facets (sys : InequalitySystem Space Row) : (facets sys.body).Finite := by
  apply (Set.finite_range sys.locus).subset
  intro face hf
  obtain ⟨point, _, he⟩ := face_eq_locus hf.1 hf.2.1
  exact ⟨_, he.symm⟩

/-- In a regular system, every set of rows active at a common point is exactly the set of rows
active at some point of the body. -/
theorem IsRegular.realize (reg : sys.IsRegular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    ∃ other ∈ sys.body, sys.active other = rows := by
  classical
  obtain ⟨dir, hd⟩ := reg point hp fun row => if row ∈ rows then 0 else 1
  have hn : ∀ row ∈ sys.active point, 0 ≤ sys.normal row dir := by
    intro row hh
    rw [hd row hh]
    split <;> norm_num
  obtain ⟨scale, _, hf, he⟩ := exists_pos_step hp hn
  refine ⟨_, hf, he.trans ?_⟩
  ext row
  by_cases hh : row ∈ sys.active point
  · simp [hh, hd row hh]
  · simp [hh, mt (fun hm => hr hm) hh]

/-- In a regular system, distinct used rows have distinct walls. -/
theorem IsRegular.injOn_wall (reg : sys.IsRegular) : InjOn sys.wall sys.used := by
  intro first hf last _ he
  obtain ⟨point, hp, hh⟩ := hf
  obtain ⟨other, ho, heq⟩ := reg.realize hp (singleton_subset_iff.mpr hh)
  have hm : other ∈ sys.wall last :=
    he ▸ (show other ∈ sys.wall first from ⟨ho, heq.symm.subset⟩)
  exact (mem_singleton_iff.mp (heq ▸ hm.2 (mem_singleton last))).symm

variable [FiniteDimensional ℝ Space]

/-- In a regular system, `k` rows active at a common point leave a space of directions of
dimension `finrank - k`. -/
theorem IsRegular.rank (reg : sys.IsRegular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    rows.ncard + finrank ℝ (sys.directions rows) = finrank ℝ Space := by
  classical
  let := Fintype.ofFinite rows
  have he := (sys.evaluation rows).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (reg.surjective hp hr), finrank_top, finrank_pi,
    fintypeCard_eq_ncard, ker_evaluation] at he
  exact he

/-- In a regular system, the locus of `k` rows active at a common point has affine dimension
`finrank - k`. -/
theorem IsRegular.dim_locus (reg : sys.IsRegular) (hp : point ∈ sys.body)
    (hr : rows ⊆ sys.active point) :
    rows.ncard + affineDim (sys.locus rows) = finrank ℝ Space := by
  obtain ⟨other, ho, rfl⟩ := reg.realize hp hr
  rw [affineDim, vectorSpan_active ho]
  exact reg.rank ho Subset.rfl

/-- The nonempty body of a regular system is full-dimensional. -/
theorem IsRegular.dim_body (reg : sys.IsRegular) (hne : sys.body.Nonempty) :
    affineDim sys.body = finrank ℝ Space := by
  obtain ⟨point, hp⟩ := hne
  simpa [locus] using reg.dim_locus hp (empty_subset _)

/-- In a regular system, the vertices are the points of the body with `finrank` active rows. -/
theorem IsRegular.vertex_card (reg : sys.IsRegular) (hp : point ∈ sys.body) :
    point ∈ sys.body.extremePoints ℝ ↔ (sys.active point).ncard = finrank ℝ Space := by
  have he := reg.rank hp Subset.rfl
  rw [vertex_iff hp, ← Submodule.finrank_eq_zero]
  omega

/-- In a regular system, the facets of the body are the walls of the used rows. -/
theorem IsRegular.facets_eq (reg : sys.IsRegular) :
    facets sys.body = sys.wall '' sys.used := by
  ext face
  constructor
  · rintro ⟨hf, hne, hd⟩
    obtain ⟨point, hp, he⟩ := face_eq_locus hf hne
    have hb := hf.1.subset hp
    have hc := reg.dim_locus hb Subset.rfl
    rw [reg.dim_body ⟨point, hb⟩, he] at hd
    obtain ⟨row, hr⟩ := ncard_eq_one.mp (show (sys.active point).ncard = 1 by omega)
    exact ⟨row, ⟨point, hb, hr.symm ▸ mem_singleton row⟩, by simp [he, hr, wall]⟩
  · rintro ⟨row, ⟨point, hp, hr⟩, rfl⟩
    have hh := singleton_subset_iff.mpr hr
    refine ⟨sys.isPolytopeFace_locus _, ⟨point, hp, hh⟩, ?_⟩
    rw [reg.dim_body ⟨point, hp⟩]
    simpa [wall, Nat.add_comm] using reg.dim_locus hp hh

/-- In a regular system, the body has one facet for each used row. -/
theorem IsRegular.ncard_facets (reg : sys.IsRegular) :
    (facets sys.body).ncard = sys.used.ncard := by
  rw [reg.facets_eq, reg.injOn_wall.ncard_image]

/-- The body of a regular system is simple. -/
theorem IsRegular.isSimple (reg : sys.IsRegular) : IsSimple sys.body := by
  intro point hv
  have hs : sys.active point ⊆ sys.used := fun _ hr => ⟨point, hv.1, hr⟩
  have he : {face ∈ facets sys.body | point ∈ face} = sys.wall '' sys.active point := by
    rw [reg.facets_eq]
    ext face
    constructor
    · rintro ⟨⟨row, _, rfl⟩, _, hh⟩
      exact ⟨row, hh (mem_singleton row), rfl⟩
    · rintro ⟨row, hr, rfl⟩
      exact ⟨⟨row, hs hr, rfl⟩, hv.1, singleton_subset_iff.mpr hr⟩
  rw [he, (reg.injOn_wall.mono hs).ncard_image, (reg.vertex_card hv.1).mp hv,
    reg.dim_body ⟨point, hv.1⟩]

end Cslib.Polyhedra.InequalitySystem
