/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polyhedra.Polytope
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Systems of linear inequalities and their faces

A system of linear inequalities `rhs row ≤ normal row x` on a real vector space, indexed by a type
of rows (`Cslib.Polyhedra.InequalitySystem`), cuts out a convex set, its `body`. This module
describes the faces of such a body. The set where a given family of rows is tight (its `locus`) is
always a face; with finitely many rows, every nonempty face is the locus of the rows tight at one
of its points, and a point of the body is a vertex exactly when the normals of its tight rows
leave no direction free.

It also defines the affine dimension of a set, the facets of a set and simple sets, in which every
vertex lies on exactly as many facets as the affine dimension. Faces are
`Cslib.Polyhedra.IsPolytopeFace`, the convex extreme subsets.

## Main definitions

* `Cslib.Polyhedra.affineDim`: the dimension of the span of the differences of a set.
* `Cslib.Polyhedra.facets`: the nonempty faces of codimension one.
* `Cslib.Polyhedra.IsSimple`: every vertex lies on exactly `affineDim` facets.
* `Cslib.Polyhedra.InequalitySystem`: a row-indexed system `rhs row ≤ normal row x`, with its
  `body`, the rows `active` at a point, the `locus` where a set of rows is tight and the
  `directions` along which those rows stay tight.

## Main results

* `Cslib.Polyhedra.InequalitySystem.isPolytopeFace_locus`: every locus is a face.
* `Cslib.Polyhedra.InequalitySystem.face_eq_locus`: with finitely many rows, every nonempty face
  is the locus of the rows active at one of its points.
* `Cslib.Polyhedra.InequalitySystem.vectorSpan_active`: the locus of the rows active at a point
  spans exactly the directions that keep those rows tight.
* `Cslib.Polyhedra.InequalitySystem.vertex_iff`: a point of the body is a vertex if and only if
  no nonzero direction keeps its active rows tight.

## Implementation notes

This is a port of
[`Faces.lean`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Faces.lean)
from the Lean formalization accompanying [OpenAI2026Hirsch] (source revision `3344da5`).
Statements are unchanged up to the following renaming (source names are in the namespace
`OAI.Geometry.Hirsch`):

| source | here |
|---|---|
| `IsFace body face` (structure with fields `convex`, `extreme`) | `IsPolytopeFace body face` |
| `dim` | `affineDim` |
| `facets` | `facets` |
| `Simple` | `IsSimple` |
| `System`, `System.body`, `.active`, `.locus`, `.directions` | `InequalitySystem`, same fields |
| `System.isFace_locus` | `InequalitySystem.isPolytopeFace_locus` |
| `System.step` | `InequalitySystem.exists_pos_step` |
| `System.step_directions` | `InequalitySystem.exists_pos_step_mem_locus` |

All other declarations keep their source names under `Cslib.Polyhedra.InequalitySystem`.
`IsPolytopeFace body face` unfolds to `IsExtreme ℝ body face ∧ Convex ℝ face`, the source's two
fields in the other order.

## References

* [OpenAI2026Hirsch]
-/

@[expose] public section

noncomputable section

open Set Filter Module
open scoped Topology

namespace Cslib.Polyhedra

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

/-- The **affine dimension** of a set: the dimension of the span of its differences
(`vectorSpan`). The empty set and single points have affine dimension `0`. -/
def affineDim (s : Set Space) : ℕ := finrank ℝ (vectorSpan ℝ s)

/-- The **facets** of `body`: its nonempty faces whose affine dimension is one less than that of
`body`. -/
def facets (body : Set Space) : Set (Set Space) :=
  {face | IsPolytopeFace body face ∧ face.Nonempty ∧ affineDim face + 1 = affineDim body}

/-- A set is **simple** when each of its vertices (extreme points) lies on exactly as many facets
as its affine dimension. -/
def IsSimple (body : Set Space) : Prop :=
  ∀ point ∈ body.extremePoints ℝ, {face ∈ facets body | point ∈ face}.ncard = affineDim body

/-- A **system of linear inequalities** `rhs row ≤ normal row x` on a real vector space, one for
each element of a type `Row` of rows. -/
structure InequalitySystem (Space : Type*) [AddCommGroup Space] [Module ℝ Space]
    (Row : Type*) where
  /-- The linear form on the right of each inequality. -/
  normal : Row → Space →ₗ[ℝ] ℝ
  /-- The constant on the left of each inequality. -/
  rhs : Row → ℝ

namespace InequalitySystem

variable {Row : Type*} (sys : InequalitySystem Space Row)

/-- The **body** of a system: the points satisfying every inequality. -/
def body : Set Space := {point | ∀ row, sys.rhs row ≤ sys.normal row point}

/-- The rows **active** (tight) at a point: those holding with equality there. -/
def active (point : Space) : Set Row :=
  {row | sys.normal row point = sys.rhs row}

/-- The **locus** of a set of rows: the points of the body at which all of them are active. -/
def locus (rows : Set Row) : Set Space :=
  {point ∈ sys.body | rows ⊆ sys.active point}

/-- The **directions** of a set of rows: the vectors on which all of their normals vanish, that is,
the directions of motion that keep those rows tight. -/
def directions (rows : Set Row) : Submodule ℝ Space :=
  ⨅ row ∈ rows, (sys.normal row).ker

/-- A direction keeps a set of rows tight when every one of their normals vanishes on it. -/
theorem mem_directions {rows : Set Row} {dir : Space} :
    dir ∈ sys.directions rows ↔ ∀ row ∈ rows, sys.normal row dir = 0 := by
  simp [directions, LinearMap.mem_ker]

variable {sys} {first last point dir : Space} {rows : Set Row}

/-- The difference of two points at which a set of rows is active keeps those rows tight. -/
theorem sub_mem_directions (hf : rows ⊆ sys.active first) (hl : rows ⊆ sys.active last) :
    first - last ∈ sys.directions rows := by
  refine sys.mem_directions.mpr fun row hr => ?_
  rw [map_sub, show sys.normal row first = _ from hf hr,
    show sys.normal row last = _ from hl hr, sub_self]

/-- The locus of a set of rows spans only directions that keep those rows tight. -/
theorem vectorSpan_locus_le :
    vectorSpan ℝ (sys.locus rows) ≤ sys.directions rows := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨first, hf, last, hl, rfl⟩
  exact sub_mem_directions hf.2 hl.2

/-- The body of a system is convex. -/
theorem convex_body (sys : InequalitySystem Space Row) : Convex ℝ sys.body := by
  intro first hf last hl left right hleft hright hsum row
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  calc
    _ = left * sys.rhs row + right * sys.rhs row := by rw [← add_mul, hsum, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hf row) hleft)
      (mul_le_mul_of_nonneg_left (hl row) hright)

/-- At a point strictly between two points of the body, the active rows are those active at both
endpoints. -/
theorem active_openSegment (hf : first ∈ sys.body) (hl : last ∈ sys.body)
    (hp : point ∈ openSegment ℝ first last) :
    sys.active point = sys.active first ∩ sys.active last := by
  obtain ⟨left, right, hleft, hright, hsum, rfl⟩ := hp
  ext row
  simp only [active, mem_ofPred_eq, mem_inter_iff, map_add, map_smul, smul_eq_mul]
  have eqn : left * sys.rhs row + right * sys.rhs row = sys.rhs row := by
    rw [← add_mul, hsum, one_mul]
  constructor
  · intro heq
    constructor
    · apply le_antisymm _ (hf row)
      apply le_of_mul_le_mul_left _ hleft
      linarith [mul_le_mul_of_nonneg_left (hl row) hright.le]
    · apply le_antisymm _ (hl row)
      apply le_of_mul_le_mul_left _ hright
      linarith [mul_le_mul_of_nonneg_left (hf row) hleft.le]
  · rintro ⟨he, he'⟩
    rw [he, he', eqn]

/-- Every locus is a face of the body. -/
theorem isPolytopeFace_locus (sys : InequalitySystem Space Row) (rows : Set Row) :
    IsPolytopeFace sys.body (sys.locus rows) := by
  refine ⟨⟨fun _ hp => hp.1, fun _ hf _ hl _ hp hseg => ⟨hf, ?_⟩⟩, ?_⟩
  · exact hp.2.trans ((active_openSegment hf hl hseg).subset.trans inter_subset_left)
  · intro first hf last hl left right hleft hright hsum
    refine ⟨sys.convex_body hf.1 hl.1 hleft hright hsum, fun row hr => ?_⟩
    change sys.normal row _ = _
    rw [map_add, map_smul, map_smul, show sys.normal row first = _ from hf.2 hr,
      show sys.normal row last = _ from hl.2 hr, ← add_smul, hsum, one_smul]

variable [Finite Row]

/-- From a point of the body, a short step along a direction that does not decrease any active
row stays in the body, and the rows active after the step are the active rows on which the
direction vanishes. -/
theorem exists_pos_step (hp : point ∈ sys.body)
    (hd : ∀ row ∈ sys.active point, 0 ≤ sys.normal row dir) :
    ∃ scale : ℝ, 0 < scale ∧ point + scale • dir ∈ sys.body ∧
      sys.active (point + scale • dir) =
        {row ∈ sys.active point | sys.normal row dir = 0} := by
  have hev : ∀ᶠ scale : ℝ in 𝓝 0, ∀ row ∉ sys.active point,
      sys.rhs row < sys.normal row (point + scale • dir) := by
    apply eventually_all.mpr
    intro row
    by_cases hr : row ∈ sys.active point
    · exact Eventually.of_forall fun _ hn => (hn hr).elim
    have hlt : sys.rhs row < sys.normal row point := lt_of_le_of_ne (hp row) (Ne.symm hr)
    have hc : Continuous (fun scale : ℝ => sys.normal row point + scale * sys.normal row dir) :=
      continuous_const.add (continuous_id.mul continuous_const)
    have hh := hc.continuousAt (x := (0 : ℝ))
    filter_upwards [hh.eventually (eventually_gt_nhds (by simpa using hlt))] with scale hs _
    simpa using hs
  obtain ⟨scale, hs, he⟩ := (eventually_mem_nhdsWithin.and
    (hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ scale in 𝓝[>] (0 : ℝ), scale ∈ Ioi 0 ∧ _).exists
  change 0 < scale at hs
  refine ⟨scale, hs, ?_, ?_⟩
  · intro row
    by_cases hr : row ∈ sys.active point
    · rw [map_add, map_smul, smul_eq_mul, show sys.normal row point = _ from hr]
      exact le_add_of_nonneg_right (mul_nonneg hs.le (hd row hr))
    · exact (he row hr).le
  · ext row
    by_cases hr : row ∈ sys.active point
    · change sys.normal row point = sys.rhs row at hr
      simp [active, hr, hs.ne']
    · exact iff_of_false (he row hr).ne' (fun hh => hr hh.1)

/-- From a point of the body, a short step along a direction keeping its active rows tight stays
in the locus of those rows. -/
theorem exists_pos_step_mem_locus (hp : point ∈ sys.body)
    (hd : dir ∈ sys.directions (sys.active point)) :
    ∃ scale : ℝ, 0 < scale ∧ point + scale • dir ∈ sys.locus (sys.active point) := by
  have hz := sys.mem_directions.mp hd
  obtain ⟨scale, hs, hf, he⟩ := exists_pos_step hp (fun row hr => (hz row hr).ge)
  exact ⟨scale, hs, hf, he.symm ▸ fun row hr => ⟨hr, hz row hr⟩⟩

/-- The locus of the rows active at a point of the body spans exactly the directions that keep
those rows tight. -/
theorem vectorSpan_active (hp : point ∈ sys.body) :
    vectorSpan ℝ (sys.locus (sys.active point)) = sys.directions (sys.active point) := by
  apply le_antisymm vectorSpan_locus_le
  intro dir hd
  obtain ⟨scale, hs, hf⟩ := exists_pos_step_mem_locus hp hd
  have hh := vsub_mem_vectorSpan ℝ hf
    (show point ∈ sys.locus (sys.active point) from ⟨hp, Subset.rfl⟩)
  rw [vsub_eq_sub, add_sub_cancel_left] at hh
  simpa [smul_smul, hs.ne'] using (vectorSpan ℝ _).smul_mem scale⁻¹ hh

/-- An extreme subset of the body containing a point contains the locus of the rows active
there. -/
theorem locus_minimal {face : Set Space} (he : IsExtreme ℝ sys.body face) (hp : point ∈ face) :
    sys.locus (sys.active point) ⊆ face := by
  intro first hf
  obtain ⟨scale, hs, hl⟩ := exists_pos_step_mem_locus (he.subset hp)
    (sub_mem_directions (first := point) Subset.rfl hf.2)
  apply he.left_mem_of_mem_openSegment hf.1 hl.1 hp
  have hpos : 0 < 1 + scale := by linarith
  refine ⟨scale / (1 + scale), 1 / (1 + scale), div_pos hs hpos,
    div_pos one_pos hpos, by rw [← add_div, add_comm scale, div_self hpos.ne'], ?_⟩
  match_scalars <;> field_simp
  ring

/-- Every nonempty face of the body is the locus of the rows active at one of its points. -/
theorem face_eq_locus {face : Set Space} (hf : IsPolytopeFace sys.body face)
    (hne : face.Nonempty) :
    ∃ point ∈ face, face = sys.locus (sys.active point) := by
  obtain ⟨point, hp, hmin⟩ := (measure fun point => (sys.active point).ncard).wf.has_min face hne
  refine ⟨point, hp, Subset.antisymm ?_ (locus_minimal hf.1 hp)⟩
  intro last hl
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hm := hf.2.midpoint_mem hp hl
  have he := active_openSegment (hf.1.subset hp) (hf.1.subset hl)
    (midpoint_mem_openSegment point last (𝕜 := ℝ))
  have hc : (sys.active point).ncard ≤ (sys.active (midpoint ℝ point last)).ncard :=
    Nat.le_of_not_gt (hmin _ hm)
  rw [he] at hc
  have eqn := Set.eq_of_subset_of_ncard_le inter_subset_left hc
  exact ⟨hf.1.subset hl, eqn.symm.subset.trans inter_subset_right⟩

/-- A point of the body is a vertex if and only if no nonzero direction keeps its active rows
tight. -/
theorem vertex_iff (hp : point ∈ sys.body) :
    point ∈ sys.body.extremePoints ℝ ↔ sys.directions (sys.active point) = ⊥ := by
  rw [← vectorSpan_active hp, vectorSpan_eq_bot_iff_subsingleton]
  constructor
  · intro hv
    have he : IsExtreme ℝ sys.body {point} :=
      ⟨singleton_subset_iff.mpr hp, by rintro _ hf _ hl _ rfl hs; exact hv.2 hf hl hs⟩
    exact subsingleton_singleton.anti (locus_minimal he (mem_singleton point))
  · intro hh
    refine ⟨hp, fun _ hf _ hl hs => hh ?_ ⟨hp, Subset.rfl⟩⟩
    exact ⟨hf, (active_openSegment hf hl hs).subset.trans inter_subset_left⟩

end InequalitySystem

end Cslib.Polyhedra
