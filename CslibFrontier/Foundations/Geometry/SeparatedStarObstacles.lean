/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.PathConnected
import CslibFrontier.Foundations.Geometry.StarConvexEscape
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Paths around star-convex obstacles in separated rectangles

A point in a rectangle escapes along a segment from the star center's direction. Outside
the open rectangles, horizontal and vertical segments connect the escapes through a
vertical line missing all the rectangles. The boundaries are available to these paths.
-/

public section

namespace Cslib

private theorem isPathConnected_outside_vertical_band (A : Set ℝ) {x : ℝ} (hx : x ∉ A)
    (bottom top : ℝ) : IsPathConnected {z : ℂ | ¬(z.re ∈ A ∧ z.im ∈ Set.Ioo bottom top)} := by
  let U : Set ℂ := {z | ¬(z.re ∈ A ∧ z.im ∈ Set.Ioo bottom top)}
  have along (f : ℂ →ₗ[ℝ] ℝ) (z w : ℂ) (hw : f w = f z) (h : ∀ p, f p = f z → p ∈ U) :
      JoinedIn U z w :=
    JoinedIn.of_segment_subset fun p hp =>
      h p (((convex_singleton (𝕜 := ℝ) (f z)).linear_preimage f).segment_subset rfl hw hp)
  have vert (z : ℂ) (hz : z.re ∉ A) (y : ℝ) : JoinedIn U z ⟨z.re, y⟩ :=
    along Complex.reCLM.toLinearMap z ⟨z.re, y⟩ rfl fun p hp hb =>
      hz ((show p.re = z.re from hp) ▸ hb.1)
  have horiz (z : ℂ) (hz : z.im ∉ Set.Ioo bottom top) : JoinedIn U z ⟨x, z.im⟩ :=
    along Complex.imCLM.toLinearMap z ⟨x, z.im⟩ rfl fun p hp hb =>
      hz ((show p.im = z.im from hp) ▸ hb.2)
  refine ⟨⟨x, top⟩, fun h => hx h.1, fun z hz => ?_⟩
  by_cases h : z.re ∈ A
  · exact ((horiz z fun hh => hz ⟨h, hh⟩).trans (vert ⟨x, z.im⟩ hx top)).symm
  · exact ((vert z h top).trans (horiz ⟨z.re, top⟩ fun ht => lt_irrefl top ht.2)).symm

/-- The complement of star-convex obstacles in horizontally separated open rectangles is
path connected. All rectangles have the same vertical bounds, and a single vertical line
is assumed available outside their open horizontal intervals. -/
theorem isPathConnected_compl_iUnion_starConvex_of_separated_rectangles {ι : Type*}
    (S : ι → Set ℂ) (center : ι → ℂ) (left right : ι → ℝ) (bottom top : ℝ)
    (hstar : ∀ i, StarConvex ℝ (center i) (S i)) (hcenter : ∀ i, center i ∈ S i)
    (hinside : ∀ i z, z ∈ S i →
      z.re ∈ Set.Ioo (left i) (right i) ∧ z.im ∈ Set.Ioo bottom top)
    (hsep : Pairwise fun i j =>
      Disjoint (Set.Icc (left i) (right i)) (Set.Icc (left j) (right j)))
    {x : ℝ} (hgap : ∀ i, x ∉ Set.Ioo (left i) (right i)) :
    IsPathConnected (⋃ i, S i)ᶜ := by
  classical
  let A := ⋃ i, Set.Ioo (left i) (right i)
  let U : Set ℂ := {z | ¬(z.re ∈ A ∧ z.im ∈ Set.Ioo bottom top)}
  let W := (⋃ i, S i)ᶜ
  have hUW : U ⊆ W := fun z hz hb =>
    let ⟨i, hi⟩ := Set.mem_iUnion.mp hb
    hz ⟨Set.mem_iUnion.mpr ⟨i, (hinside i z hi).1⟩, (hinside i z hi).2⟩
  let box (i : ι) : Set ℂ := {z | z.re ∈ Set.Icc (left i) (right i) ∧ z.im ∈ Set.Icc bottom top}
  have compactBox (i : ι) : IsCompact (box i) :=
    Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
  have convexBox (i : ι) : Convex ℝ (box i) :=
    ((convex_Icc _ _).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Icc _ _).linear_preimage Complex.imCLM.toLinearMap)
  have boundary_clear (i : ι) {y : ℂ} (hy : y ∈ frontier (box i)) : y ∈ U := by
    obtain ⟨hybox, hyint⟩ : y ∈ box i \ interior (box i) :=
      (compactBox i).isClosed.frontier_eq ▸ hy
    rintro ⟨hre, him⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hre
    by_cases he : i = j
    · subst j
      exact hyint <| ((((isOpen_Ioo (a := left i) (b := right i)).preimage
        Complex.continuous_re).inter ((isOpen_Ioo (a := bottom) (b := top)).preimage
          Complex.continuous_im)).subset_interior_iff (t := box i) |>.mpr
            fun _ hz => ⟨Set.Ioo_subset_Icc_self hz.1, Set.Ioo_subset_Icc_self hz.2⟩) ⟨hj, him⟩
    · exact Set.disjoint_left.mp (hsep he) hybox.1 (Set.Ioo_subset_Icc_self hj)
  obtain ⟨a, ha, hconnect⟩ := isPathConnected_outside_vertical_band A
    (fun h => (Set.mem_iUnion.mp h).elim hgap) bottom top
  refine ⟨a, hUW ha, fun z hz => ?_⟩
  by_cases hzU : z ∈ U
  · exact (hconnect hzU).mono hUW
  · obtain ⟨⟨i, hi⟩, him⟩ : (∃ i, z.re ∈ Set.Ioo (left i) (right i)) ∧ z.im ∈ Set.Ioo bottom top :=
      by simpa only [U, Set.mem_ofPred_eq, not_not, A, Set.mem_iUnion] using hzU
    obtain ⟨y, hy, hseg⟩ := exists_segment_to_frontier_avoiding_starConvex (compactBox i)
      (convexBox i) (hstar i) (hcenter i) ⟨Set.Ioo_subset_Icc_self hi, Set.Ioo_subset_Icc_self him⟩
      fun h => hz (Set.mem_iUnion.mpr ⟨i, h⟩)
    refine ((hconnect (boundary_clear i hy)).mono hUW).trans (JoinedIn.of_segment_subset ?_).symm
    intro w hw hbad
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbad
    by_cases he : i = j
    · subst he
      exact (hseg hw).2 hj
    · exact Set.disjoint_left.mp (hsep he) (hseg hw).1.1
        (Set.Ioo_subset_Icc_self (hinside j w hj).1)

end Cslib
