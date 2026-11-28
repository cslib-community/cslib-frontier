/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

import CslibFrontier.Foundations.Geometry.Polyhedra.Hirsch
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Tests for rational H-polytopes, face graphs and the Hirsch statements

The unit square `[0, 1]^2`, given by the four inequalities `0 ≤ x i` and `-1 ≤ -x i`, is a
`RationalHPolytope` with a regular presentation. The tests check that it is simple, has
dimension `2` and four facets, that its vertices are the four corners, that its graph is connected
with diameter `2` (opposite corners are not adjacent), and that `x 0 + x 1` is an objective whose
extreme vertices are opposite corners, giving an `Example`. They also elaborate
`not_polynomialHirsch_of_main`.
-/

namespace CslibFrontierTests.PolyhedraHirsch

open Set Module Cslib.Polyhedra

/-- The unit square: row `(i, false)` is `0 ≤ x i` and row `(i, true)` is `-1 ≤ -x i`. -/
noncomputable def squareSystem : InequalitySystem (Fin 2 → ℝ) (Fin 2 × Bool) where
  normal row := bif row.2 then -LinearMap.proj row.1 else LinearMap.proj row.1
  rhs row := bif row.2 then -1 else 0

theorem normal_false (i : Fin 2) (x : Fin 2 → ℝ) : squareSystem.normal (i, false) x = x i := rfl

theorem normal_true (i : Fin 2) (x : Fin 2 → ℝ) : squareSystem.normal (i, true) x = -x i := rfl

theorem rhs_false (i : Fin 2) : squareSystem.rhs (i, false) = 0 := rfl

theorem rhs_true (i : Fin 2) : squareSystem.rhs (i, true) = -1 := rfl

theorem mem_active_false {i : Fin 2} {x : Fin 2 → ℝ} :
    (i, false) ∈ squareSystem.active x ↔ x i = 0 := by
  simp [InequalitySystem.active, normal_false, rhs_false]

theorem mem_active_true {i : Fin 2} {x : Fin 2 → ℝ} :
    (i, true) ∈ squareSystem.active x ↔ x i = 1 := by
  simp [InequalitySystem.active, normal_true, rhs_true]

theorem mem_body {x : Fin 2 → ℝ} : x ∈ squareSystem.body ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp [InequalitySystem.body, Prod.forall, Bool.forall_bool, normal_false, normal_true,
    rhs_false, rhs_true]

theorem body_eq : squareSystem.body = Icc 0 1 := by
  ext x
  simp [mem_body, Pi.le_def, forall_and]

/-- The presentation of the square is regular: at each point, at most one row per coordinate is
active, so the active normals are independent. -/
theorem isRegular : squareSystem.IsRegular := by
  intro x _ values
  refine ⟨fun i => if x i = 0 then values (i, false) else -values (i, true), ?_⟩
  rintro ⟨i, b⟩ hb
  cases b
  · rw [mem_active_false] at hb
    simp [normal_false, hb]
  · rw [mem_active_true] at hb
    simp [normal_true, hb]

/-- The unit square as a bounded rational polytope given by inequalities. -/
noncomputable abbrev square : RationalHPolytope where
  Space := Fin 2 → ℝ
  Coord := Fin 2
  basis := Pi.basisFun ℝ (Fin 2)
  Row := Fin 2 × Bool
  sys := squareSystem
  rationalNormal := by
    rintro ⟨i, b⟩ j
    refine ⟨(bif b then -1 else 1) * (if i = j then 1 else 0), ?_⟩
    cases b <;> by_cases h : i = j <;> simp [normal_false, normal_true, h]
  rationalRhs := by
    rintro ⟨i, b⟩
    exact ⟨bif b then -1 else 0, by cases b <;> simp [rhs_false, rhs_true]⟩
  compact := by rw [body_eq]; exact isCompact_Icc
  nonempty := ⟨0, mem_body.mpr fun _ => by simp⟩

/-! ### Simplicity, dimension and facets -/

example : IsSimple square.body := isRegular.isSimple

example : square.dimension = 2 := by
  rw [RationalHPolytope.dimension, isRegular.dim_body square.nonempty, finrank_fin_fun]

/-- Every row is active somewhere: at the corner `0` for `(i, false)` and `1` for `(i, true)`. -/
theorem used_eq_univ : squareSystem.used = univ := by
  refine eq_univ_of_forall fun ⟨i, b⟩ => ?_
  cases b
  · exact ⟨0, mem_body.mpr fun _ => by simp, mem_active_false.mpr rfl⟩
  · exact ⟨1, mem_body.mpr fun _ => by simp, mem_active_true.mpr rfl⟩

example : square.facetCount = 4 := by
  rw [RationalHPolytope.facetCount, isRegular.ncard_facets, used_eq_univ, ncard_univ]
  simp

example : IsPolytope square.body := square.isPolytope

/-! ### Vertices -/

/-- The vertices of the square are its four corners. -/
theorem mem_extremePoints {x : Fin 2 → ℝ} :
    x ∈ squareSystem.body.extremePoints ℝ ↔ ∀ i, x i = 0 ∨ x i = 1 := by
  constructor
  · intro hv i
    have hb := (InequalitySystem.vertex_iff hv.1).mp hv
    by_contra! hi
    have hd : Pi.single i 1 ∈ squareSystem.directions (squareSystem.active x) := by
      refine squareSystem.mem_directions.mpr fun ⟨j, b⟩ hr => ?_
      have hj : j ≠ i := by
        rintro rfl
        cases b
        · exact hi.1 (mem_active_false.mp hr)
        · exact hi.2 (mem_active_true.mp hr)
      cases b <;> simp [normal_false, normal_true, hj]
    rw [hb, Submodule.mem_bot] at hd
    simpa using congrFun hd i
  · intro hx
    have hb : x ∈ squareSystem.body :=
      mem_body.mpr fun i => by rcases hx i with h | h <;> simp [h]
    refine (InequalitySystem.vertex_iff hb).mpr (eq_bot_iff.mpr fun d hd => ?_)
    rw [Submodule.mem_bot]
    funext i
    have hz := squareSystem.mem_directions.mp hd
    rcases hx i with h | h
    · simpa [normal_false] using hz (i, false) (mem_active_false.mpr h)
    · simpa [normal_true] using hz (i, true) (mem_active_true.mpr h)

/-- The corner of the square with coordinates `x`, each `0` or `1`. -/
def corner (x : Fin 2 → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) : square.V :=
  ⟨x, mem_extremePoints.mpr hx⟩

/-! ### The graph -/

theorem connected : (faceGraph square.body 1).Connected := square.connected isRegular le_rfl

/-- Two corners agreeing in one coordinate share an active row, so they are equal or adjacent. -/
theorem dist_le_one_of_eq {u v : square.V} (i : Fin 2) (h : u.val i = v.val i) :
    square.dist 1 u v ≤ 1 := by
  by_cases huv : u = v
  · simp [huv]
  refine (SimpleGraph.dist_eq_one_iff_adj.mpr ((square.adj_iff isRegular).mpr ⟨huv, ?_⟩)).le
  have hrow : ∃ b, (i, b) ∈ squareSystem.active u.val ∩ squareSystem.active v.val := by
    rcases mem_extremePoints.mp u.property i with hu | hu
    · exact ⟨false, mem_active_false.mpr hu, mem_active_false.mpr (h.symm.trans hu)⟩
    · exact ⟨true, mem_active_true.mpr hu, mem_active_true.mpr (h.symm.trans hu)⟩
  obtain ⟨b, hb⟩ := hrow
  have hpos := (ncard_pos (toFinite _)).mpr ⟨_, hb⟩
  change finrank ℝ (Fin 2 → ℝ) ≤
    (squareSystem.active u.val ∩ squareSystem.active v.val).ncard + 1
  rw [finrank_fin_fun]
  omega

/-- Any two vertices of the square are at distance at most `2`, through the corner that agrees
with the first in coordinate `0` and with the second in coordinate `1`. -/
theorem dist_le_two (u v : square.V) : square.dist 1 u v ≤ 2 := by
  have hu := mem_extremePoints.mp u.property
  have hv := mem_extremePoints.mp v.property
  let w := corner (fun j => if j = 0 then u.val 0 else v.val 1) fun j => by
    split
    · exact hu 0
    · exact hv 1
  calc
    square.dist 1 u v ≤ square.dist 1 u w + square.dist 1 w v := connected.dist_triangle
    _ ≤ 1 + 1 := add_le_add (dist_le_one_of_eq 0 (by simp [w, corner]))
      (dist_le_one_of_eq 1 (by simp [w, corner]))

/-- The corner `(0, 0)`. -/
def bottom : square.V := corner 0 fun _ => Or.inl rfl

/-- The corner `(1, 1)`. -/
def top : square.V := corner 1 fun _ => Or.inr rfl

/-- Opposite corners share no active row, so they are not adjacent. -/
theorem not_adj_bottom_top : ¬ (faceGraph square.body 1).Adj bottom top := by
  rw [square.adj_iff isRegular]
  rintro ⟨-, h⟩
  have hempty : squareSystem.active (0 : Fin 2 → ℝ) ∩ squareSystem.active 1 = ∅ := by
    refine eq_empty_of_forall_notMem fun ⟨i, b⟩ ⟨h0, h1⟩ => ?_
    cases b
    · simp [mem_active_false] at h1
    · simp [mem_active_true] at h0
  change finrank ℝ (Fin 2 → ℝ) ≤ (squareSystem.active 0 ∩ squareSystem.active 1).ncard + 1 at h
  rw [hempty, ncard_empty, finrank_fin_fun] at h
  omega

theorem dist_bottom_top : square.dist 1 bottom top = 2 := by
  have hne : bottom ≠ top := fun h => by
    simpa [bottom, top, corner] using congrFun (congrArg Subtype.val h) 0
  have h0 : square.dist 1 bottom top ≠ 0 := fun h => hne (connected.dist_eq_zero_iff.mp h)
  have h1 : square.dist 1 bottom top ≠ 1 :=
    fun h => not_adj_bottom_top (SimpleGraph.dist_eq_one_iff_adj.mp h)
  have h2 := dist_le_two bottom top
  omega

/-- The diameter of the graph of the square is `2`. -/
example : (faceGraph square.body 1).diam = 2 := by
  have hle : (faceGraph square.body 1).ediam ≤ 2 := SimpleGraph.ediam_le_iff.mpr fun u v => by
    obtain ⟨p, hp⟩ := (connected u v).exists_walk_length_eq_dist
    refine (SimpleGraph.edist_le p).trans ?_
    rw [hp]
    exact_mod_cast dist_le_two u v
  have hfin : (faceGraph square.body 1).ediam ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have hdiam : ((faceGraph square.body 1).diam : ℕ∞) ≤ 2 :=
    (SimpleGraph.natCast_diam_eq_ediam_iff.mpr hfin) ▸ hle
  have hlow := SimpleGraph.dist_le_diam (u := bottom) (v := top) hfin
  have htwo : (faceGraph square.body 1).dist bottom top = 2 := dist_bottom_top
  have hup : (faceGraph square.body 1).diam ≤ 2 := by exact_mod_cast hdiam
  omega

/-! ### An objective and an `Example` -/

/-- The linear form `x 0 + x 1`. -/
def sumForm : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

theorem sumForm_apply (x : Fin 2 → ℝ) : sumForm x = x 0 + x 1 := rfl

/-- The objective `x 0 + x 1`, minimized at `(0, 0)` and maximized at `(1, 1)`. -/
noncomputable def sumObjective : square.Objective where
  lin := sumForm
  low := bottom
  high := top
  bounds point hp := by
    have h := mem_body.mp hp
    change sumForm 0 ≤ sumForm point ∧ sumForm point ≤ sumForm 1
    simp only [sumForm_apply, Pi.zero_apply, Pi.one_apply]
    constructor <;> linarith [h 0, h 1]
  positive := by
    change sumForm 0 < sumForm 1
    norm_num [sumForm_apply]

example : sumObjective.gap sumObjective.high sumObjective.low = 1 :=
  sumObjective.gap_extremes

/-- The square with the objective `x 0 + x 1` is an `Example`, the shape of the members of the
families in `MainTheorem`. -/
noncomputable def squareExample : Hirsch.Example := ⟨square, sumObjective⟩

/-! ### The Hirsch statements -/

example : Hirsch.MainTheorem → ¬ Hirsch.PolynomialHirsch := Hirsch.not_polynomialHirsch_of_main

end CslibFrontierTests.PolyhedraHirsch
