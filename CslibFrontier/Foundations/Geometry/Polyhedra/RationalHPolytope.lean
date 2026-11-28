/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polyhedra.FaceGraph
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Bounded rational polytopes given by inequalities

A `Cslib.Polyhedra.RationalHPolytope` is a nonempty compact body cut out by finitely many linear
inequalities on a finite-dimensional real normed space whose coefficients, in a chosen basis, and
right-hand sides are rational. It records the dimension of the body, its number of facets and the
distance in each face graph, which are the quantities in the polynomial Hirsch conjecture
(`Cslib.Polyhedra.Hirsch.PolynomialHirsch`). Its body is a polytope in the sense of
`Cslib.Polyhedra.IsPolytope` (`Cslib.Polyhedra.RationalHPolytope.isPolytope`). An `Objective` is a
linear functional with chosen minimizing and maximizing vertices and positive range, and the `gap`
of two vertices is the share of that range separating their values.

## Main definitions

* `Cslib.Polyhedra.RationalHPolytope`: a nonempty bounded rational system of inequalities.
* `Cslib.Polyhedra.RationalHPolytope.dimension`, `Cslib.Polyhedra.RationalHPolytope.facetCount`,
  `Cslib.Polyhedra.RationalHPolytope.dist`: the dimension, the number of facets, and the distance
  between vertices in the face graph of a given level.
* `Cslib.Polyhedra.RationalHPolytope.Objective`, `Cslib.Polyhedra.RationalHPolytope.Objective.gap`:
  a linear objective and the normalized gap between the values of two vertices.

## Main results

* `Cslib.Polyhedra.RationalHPolytope.isPolytope`: the body is a compact convex polytope.
* `Cslib.Polyhedra.RationalHPolytope.connected`: the face graphs of level at least `1` of a regular
  presentation are connected.
* `Cslib.Polyhedra.RationalHPolytope.adj_iff`: in a regular presentation, two vertices are adjacent
  at level `moves` when they share at least `dim - moves` active rows.

## Implementation notes

This is a port of
[`Polytope.lean`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Polytope.lean)
from the Lean formalization accompanying [OpenAI2026Hirsch] (source revision `3344da5`).
The structure `OAI.Geometry.Hirsch.Polytope` is renamed `RationalHPolytope`, because it bundles a
chosen presentation by inequalities rather than a set (compare the predicate `IsPolytope`); its
fields, the abbreviations `body`, `V` and `dist`, the definitions `dimension` and `facetCount`,
the structure `Objective` with `gap`, and the theorems `connected`, `dist_anti`, `adj_iff` and
`Objective.gap_extremes` keep their source names, with `Regular` read as `IsRegular` and `graph`
as `faceGraph`. The theorem `isPolytope` is new.

## References

* [OpenAI2026Hirsch]
-/

@[expose] public section

noncomputable section

open Set Module

namespace Cslib.Polyhedra

/-- A **bounded rational polytope given by inequalities**: a finite system of linear inequalities
on a finite-dimensional real normed space, rational in a chosen basis, whose body is nonempty and
compact. -/
structure RationalHPolytope where
  /-- The ambient space. -/
  Space : Type
  [group : NormedAddCommGroup Space]
  [moduleSpace : NormedSpace ℝ Space]
  [finiteDim : FiniteDimensional ℝ Space]
  /-- The index type of the basis in which the normals are rational. -/
  Coord : Type
  /-- The basis in which the normals are rational. -/
  basis : Basis Coord ℝ Space
  /-- The index type of the inequalities. -/
  Row : Type
  [finiteRow : Finite Row]
  /-- The inequalities `sys.rhs row ≤ sys.normal row x`. -/
  sys : InequalitySystem Space Row
  /-- Every normal takes rational values on the basis. -/
  rationalNormal : ∀ row coord, ∃ value : ℚ, sys.normal row (basis coord) = value
  /-- Every right-hand side is rational. -/
  rationalRhs : ∀ row, ∃ value : ℚ, sys.rhs row = value
  /-- The body is compact. -/
  compact : IsCompact sys.body
  /-- The body is nonempty. -/
  nonempty : sys.body.Nonempty

attribute [instance] RationalHPolytope.group RationalHPolytope.moduleSpace
  RationalHPolytope.finiteDim RationalHPolytope.finiteRow

namespace RationalHPolytope

variable (poly : RationalHPolytope)

/-- The polytope as a set: the body of its inequalities. -/
abbrev body := poly.sys.body

/-- The vertices of the polytope. -/
abbrev V := Vertex poly.body

/-- The dimension of the polytope: the affine dimension of its body. -/
def dimension := affineDim poly.body

/-- The number of facets of the polytope (not the number of inequalities, some of which may be
redundant). -/
def facetCount := (facets poly.body).ncard

/-- The distance between vertices in the face graph of level `moves`, which is `0` between
vertices that are not connected. -/
abbrev dist (moves : ℕ) := (faceGraph poly.body moves).dist

instance : Nonempty poly.V := poly.compact.extremePoints_nonempty poly.nonempty |>.to_subtype
instance : Finite poly.V := poly.sys.finite_vertices.to_subtype

/-- The body of a bounded rational polytope given by inequalities is a compact convex polytope,
the convex hull of finitely many points. -/
theorem isPolytope : IsPolytope poly.body := by
  rw [IsPolytope, ← isHPolytope_iff_isVPolytope]
  refine ⟨poly.compact.isBounded, Set.range fun row =>
    AffineMap.const ℝ poly.Space (poly.sys.rhs row) - (poly.sys.normal row).toAffineMap,
    Set.finite_range _, ?_⟩
  ext point
  simp [InequalitySystem.body]

/-- The face graphs of level at least `1` of a regular presentation are connected. -/
theorem connected (reg : poly.sys.IsRegular) {moves : ℕ} (hm : 1 ≤ moves) :
    (faceGraph poly.body moves).Connected :=
  ⟨reg.preconnected poly.compact hm⟩

/-- In a regular presentation, distances do not increase with the level. -/
theorem dist_anti (reg : poly.sys.IsRegular) {small large : ℕ}
    (hs : 1 ≤ small) (hm : small ≤ large) (first last : poly.V) :
    poly.dist large first last ≤ poly.dist small first last := by
  obtain ⟨walk, hw⟩ := (poly.connected reg hs first last).exists_walk_length_eq_dist
  simpa [hw] using SimpleGraph.dist_le (walk.mapLe (faceGraph_mono poly.body hm))

/-- In a regular presentation, two vertices are adjacent at level `moves` exactly when they are
distinct and share at least `finrank - moves` active rows. -/
theorem adj_iff (reg : poly.sys.IsRegular) {moves : ℕ} {first last : poly.V} :
    (faceGraph poly.body moves).Adj first last ↔ first ≠ last ∧
      finrank ℝ poly.Space ≤
        (poly.sys.active first.val ∩ poly.sys.active last.val).ncard + moves := by
  let common := poly.sys.active first.val ∩ poly.sys.active last.val
  have hd := reg.dim_locus first.property.1 (show common ⊆ _ from inter_subset_left)
  change _ ↔ first ≠ last ∧ finrank ℝ poly.Space ≤ common.ncard + moves
  constructor
  · rintro ⟨hn, face, hf, hm, hx, hy⟩
    obtain ⟨point, hp, he⟩ := InequalitySystem.face_eq_locus hf ⟨_, hx⟩
    rw [he] at hx hy hm
    have hc := ncard_le_ncard (show poly.sys.active point ⊆ common from subset_inter hx.2 hy.2)
    have hk := reg.dim_locus (hf.1.subset hp) Subset.rfl
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, hm⟩
    exact ⟨hn, poly.sys.locus common, poly.sys.isPolytopeFace_locus _, by omega,
      ⟨first.property.1, inter_subset_left⟩, last.property.1, inter_subset_right⟩

/-- A **linear objective** on a polytope, with a vertex minimizing it, a vertex maximizing it, and
positive range. -/
structure Objective where
  /-- The linear functional. -/
  lin : poly.Space →ₗ[ℝ] ℝ
  /-- A vertex at which `lin` is minimal. -/
  low : poly.V
  /-- A vertex at which `lin` is maximal. -/
  high : poly.V
  /-- `low` and `high` minimize and maximize `lin` over the body. -/
  bounds : ∀ point ∈ poly.body, lin low.val ≤ lin point ∧ lin point ≤ lin high.val
  /-- The range of `lin` over the body is positive. -/
  positive : lin low.val < lin high.val

/-- The **gap** between two vertices: the difference of their objective values, as a share of the
range of the objective. -/
def Objective.gap {poly : RationalHPolytope} (obj : poly.Objective) (first last : poly.V) : ℝ :=
  |obj.lin first.val - obj.lin last.val| / (obj.lin obj.high.val - obj.lin obj.low.val)

/-- The minimizing and maximizing vertices are at gap `1`. -/
theorem Objective.gap_extremes {poly : RationalHPolytope} (obj : poly.Objective) :
    obj.gap obj.high obj.low = 1 := by
  have hh := sub_pos.mpr obj.positive
  simp [gap, abs_of_pos hh, hh.ne']

end RationalHPolytope

end Cslib.Polyhedra
