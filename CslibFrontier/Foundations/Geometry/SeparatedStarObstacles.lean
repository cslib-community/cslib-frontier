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
  have along_coordinate (f : ℂ →ₗ[ℝ] ℝ) (z w : ℂ) (hw : f w = f z)
      (hclear : ∀ p : ℂ, f p = f z → p ∈ U) : JoinedIn U z w := by
    have hline := (convex_singleton (𝕜 := ℝ) (f z)).linear_preimage f
    apply JoinedIn.of_segment_subset
    intro p hp
    exact hclear p (hline.segment_subset (x := z) (y := w) rfl hw hp)
  have vertical (z : ℂ) (hz : z.re ∉ A) (y : ℝ) : JoinedIn U z ⟨z.re, y⟩ := by
    apply along_coordinate Complex.reCLM.toLinearMap z ⟨z.re, y⟩ rfl
    intro p hp hbad
    change p.re = z.re at hp
    exact hz (hp ▸ hbad.1)
  have horizontal (z : ℂ) (hz : z.im ∉ Set.Ioo bottom top) : JoinedIn U z ⟨x, z.im⟩ := by
    apply along_coordinate Complex.imCLM.toLinearMap z ⟨x, z.im⟩ rfl
    intro p hp hbad
    change p.im = z.im at hp
    exact hz (hp ▸ hbad.2)
  refine ⟨⟨x, top⟩, fun h => hx h.1, ?_⟩
  intro z hz
  by_cases h : z.re ∈ A
  · exact ((horizontal z (fun hh => hz ⟨h, hh⟩)).trans (vertical ⟨x, z.im⟩ hx top)).symm
  · exact ((vertical z h top).trans
      (horizontal ⟨z.re, top⟩ (fun ht => (lt_irrefl top) ht.2))).symm

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
  have hx : x ∉ A := by
    intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hgap i hi
  have hU : IsPathConnected U := isPathConnected_outside_vertical_band A hx bottom top
  have hUW : U ⊆ W := by
    intro z hz hbad
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hbad
    obtain ⟨hre, him⟩ := hinside i z hi
    exact hz ⟨Set.mem_iUnion.mpr ⟨i, hre⟩, him⟩
  let box (i : ι) : Set ℂ := {z | z.re ∈ Set.Icc (left i) (right i) ∧
    z.im ∈ Set.Icc bottom top}
  have compactBox (i : ι) : IsCompact (box i) := by
    change IsCompact (Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      Set.prod (Set.Icc (left i) (right i)) (Set.Icc bottom top))
    exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
      (isCompact_Icc.prod isCompact_Icc)
  have convexBox (i : ι) : Convex ℝ (box i) :=
    ((convex_Icc _ _).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Icc _ _).linear_preimage Complex.imCLM.toLinearMap)
  have boundary_clear (i : ι) {y : ℂ} (hy : y ∈ frontier (box i)) : y ∈ U := by
    rcases (show y ∈ box i \ interior (box i) from (compactBox i).isClosed.frontier_eq ▸ hy)
      with ⟨hybox, hyinterior⟩
    rintro ⟨hre, him⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hre
    by_cases he : i = j
    · subst j
      let V : Set ℂ := {z | z.re ∈ Set.Ioo (left i) (right i) ∧ z.im ∈ Set.Ioo bottom top}
      have hV : IsOpen V :=
        (isOpen_Ioo.preimage Complex.continuous_re).inter
          (isOpen_Ioo.preimage Complex.continuous_im)
      have hVBox : V ⊆ box i := fun _ hz =>
        ⟨Set.Ioo_subset_Icc_self hz.1, Set.Ioo_subset_Icc_self hz.2⟩
      have hyV : y ∈ V := ⟨hj, him⟩
      exact hyinterior (hV.subset_interior_iff.mpr hVBox hyV)
    · exact Set.disjoint_left.mp (hsep he) hybox.1 (Set.Ioo_subset_Icc_self hj)
  have join_exit (z : ℂ) (hz : z ∈ W) : ∃ y ∈ U, JoinedIn W z y := by
    by_cases hzU : z ∈ U
    · exact ⟨z, hzU, JoinedIn.refl hz⟩
    · change ¬¬(z.re ∈ A ∧ z.im ∈ Set.Ioo bottom top) at hzU
      obtain ⟨hre, him⟩ := not_not.mp hzU
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hre
      have hzbox : z ∈ box i := ⟨Set.Ioo_subset_Icc_self hi, Set.Ioo_subset_Icc_self him⟩
      have hzS : z ∉ S i := fun h => hz (Set.mem_iUnion.mpr ⟨i, h⟩)
      obtain ⟨y, hy, hseg⟩ := exists_segment_to_frontier_avoiding_starConvex
        (compactBox i) (convexBox i) (hstar i) (hcenter i) hzbox hzS
      refine ⟨y, boundary_clear i hy, JoinedIn.of_segment_subset ?_⟩
      intro w hw hbad
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbad
      by_cases he : i = j
      · subst j
        exact (hseg hw).2 hj
      · exact Set.disjoint_left.mp (hsep he) (hseg hw).1.1
          (Set.Ioo_subset_Icc_self (hinside j w hj).1)
  obtain ⟨a, ha, hconnect⟩ := hU
  refine ⟨a, hUW ha, ?_⟩
  intro z hz
  obtain ⟨y, hy, hzy⟩ := join_exit z hz
  exact ((hconnect hy).mono hUW).trans hzy.symm

end Cslib
