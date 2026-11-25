/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/Polytope.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import CslibFrontier.Foundations.LinearAlgebra.Matrix.FourierMotzkin
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact convex polytopes in finite-dimensional normed spaces

This module develops compact convex polytopes in finite-dimensional real normed spaces,
establishing the equivalence between vertex-hull representations (`IsVPolytope`) and bounded
finite half-space intersections (`IsHPolytope`), along with faces (`IsPolytopeFace`), vertex
centroids (`vertexCentroid`), and closure under intersections, products, affine images, and affine
preimages.

## Main definitions

* `Cslib.Polyhedra.IsVPolytope`: a set equal to the convex hull of finitely many points.
* `Cslib.Polyhedra.IsHPolytope`: a bounded intersection of finitely many closed half-spaces.
* `Cslib.Polyhedra.IsPolytope`: compact convex polytopes (`IsVPolytope`).
* `Cslib.Polyhedra.IsPolytopeFace`: convex extreme subsets of a set.
* `Cslib.Polyhedra.vertexCentroid`: the centroid of the extreme points of a polytope.

## Main results

* `Cslib.Polyhedra.isHPolytope_iff_isVPolytope`: **Weyl–Minkowski theorem** for bounded polytopes,
  proved via Fourier–Motzkin elimination (`Matrix.FourierMotzkin.exists_projection`) and
  Krein–Milman (`closure_convexHull_extremePoints`).
* `Cslib.Polyhedra.IsPolytope.inter`, `Cslib.Polyhedra.IsPolytope.prod`,
  `Cslib.Polyhedra.IsPolytope.image`, `Cslib.Polyhedra.IsPolytope.preimage_inter`,
  `Cslib.Polyhedra.IsPolytope.pi`: closure of compact convex polytopes.
* `Cslib.Polyhedra.IsPolytopeFace.isExposed`, `Cslib.Polyhedra.IsPolytopeFace.isPolytope`: faces of
  polytopes are exposed and are themselves polytopes.
* `Cslib.Polyhedra.exists_isPolytopeFace_inter_eq`,
  `Cslib.Polyhedra.exists_isPolytopeFace_prod_eq`,
  `Cslib.Polyhedra.exists_isPolytopeFace_preimage_inter_eq`: characterization of faces of
  intersections, products, and affine preimage intersections.
* `Cslib.Polyhedra.vertexCentroid_notMem_of_ssubset`,
  `Cslib.Polyhedra.vertexCentroid_notMem_affineSpan_of_ssubset`: the vertex centroid of a polytope
  lies outside every proper face and its affine span.
* `Cslib.Polyhedra.exists_isPolytopeFace_ssubset_of_ne_vertexCentroid`: ray projection from the
  vertex centroid onto a proper face.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
-/

public section

namespace Cslib.Polyhedra

open Set Finset
open scoped Matrix

section BasicDefs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A set in `E` is a **V-polytope** if it is the convex hull of a finite set of points. -/
@[expose] def IsVPolytope (P : Set E) : Prop :=
  ∃ S : Set E, S.Finite ∧ P = convexHull ℝ S

/-- A set in `E` is a bounded **H-polytope** if it is bounded and cut out by finitely many affine
inequalities `ℓ x ≤ 0`. -/
@[expose] def IsHPolytope (P : Set E) : Prop :=
  Bornology.IsBounded P ∧ ∃ L : Set (E →ᵃ[ℝ] ℝ), L.Finite ∧ P = {x | ∀ ℓ ∈ L, ℓ x ≤ 0}

/-- A **compact convex polytope** in `E` (`IsVPolytope`, equivalent to `IsHPolytope` in finite
dimensions). -/
@[expose] def IsPolytope (P : Set E) : Prop :=
  IsVPolytope P

/-- A **face** of a convex set `P` is a convex extreme subset of `P`. For polytopes, this coincides
with exposed faces (`IsPolytopeFace.isExposed`). -/
@[expose] def IsPolytopeFace (P F : Set E) : Prop :=
  IsExtreme ℝ P F ∧ Convex ℝ F

/-- The **vertex centroid** of a polytope `P`, defined as the centroid of its finite set of extreme
points (or `0` when `P.extremePoints ℝ` is infinite). -/
noncomputable def vertexCentroid (P : Set E) : E :=
  open Classical in
  if h : (P.extremePoints ℝ).Finite then h.toFinset.centroid ℝ id else 0

/-! ### Basic properties of V-polytopes and H-polytopes -/

theorem isVPolytope_empty : IsVPolytope (∅ : Set E) :=
  ⟨∅, finite_empty, convexHull_empty.symm⟩

theorem isVPolytope_singleton (x : E) : IsVPolytope ({x} : Set E) :=
  ⟨{x}, finite_singleton x, (convexHull_singleton x).symm⟩

theorem isVPolytope_convexHull {S : Set E} (hS : S.Finite) : IsVPolytope (convexHull ℝ S) :=
  ⟨S, hS, rfl⟩

theorem IsVPolytope.convex {P : Set E} (hP : IsVPolytope P) : Convex ℝ P := by
  rcases hP with ⟨S, _, rfl⟩
  exact convex_convexHull ℝ S

theorem IsVPolytope.isCompact {P : Set E} (hP : IsVPolytope P) : IsCompact P := by
  rcases hP with ⟨S, hS, rfl⟩
  exact hS.isCompact_convexHull ℝ

theorem IsVPolytope.isClosed {P : Set E} (hP : IsVPolytope P) : IsClosed P :=
  hP.isCompact.isClosed

theorem IsVPolytope.isBounded {P : Set E} (hP : IsVPolytope P) : Bornology.IsBounded P :=
  hP.isCompact.isBounded

theorem IsVPolytope.image {P : Set E} (hP : IsVPolytope P) (f : E →ᵃ[ℝ] F) :
    IsVPolytope (f '' P) := by
  rcases hP with ⟨S, hS, rfl⟩
  exact ⟨f '' S, hS.image f, f.image_convexHull S⟩

theorem IsVPolytope.prod {P : Set E} {Q : Set F} (hP : IsVPolytope P) (hQ : IsVPolytope Q) :
    IsVPolytope (P ×ˢ Q) := by
  rcases hP with ⟨S, hS, rfl⟩
  rcases hQ with ⟨T, hT, rfl⟩
  exact ⟨S ×ˢ T, hS.prod hT, (convexHull_prod S T).symm⟩

theorem isPolytope_empty : IsPolytope (∅ : Set E) := isVPolytope_empty

theorem isPolytope_singleton (x : E) : IsPolytope ({x} : Set E) := isVPolytope_singleton x

theorem isPolytope_convexHull {S : Set E} (hS : S.Finite) : IsPolytope (convexHull ℝ S) :=
  isVPolytope_convexHull hS

theorem IsPolytope.convex {P : Set E} (hP : IsPolytope P) : Convex ℝ P :=
  IsVPolytope.convex hP

theorem IsPolytope.isCompact {P : Set E} (hP : IsPolytope P) : IsCompact P :=
  IsVPolytope.isCompact hP

theorem IsPolytope.isClosed {P : Set E} (hP : IsPolytope P) : IsClosed P :=
  IsVPolytope.isClosed hP

theorem IsPolytope.isBounded {P : Set E} (hP : IsPolytope P) : Bornology.IsBounded P :=
  IsVPolytope.isBounded hP

theorem IsPolytope.prod {P : Set E} {Q : Set F} (hP : IsPolytope P) (hQ : IsPolytope Q) :
    IsPolytope (P ×ˢ Q) :=
  IsVPolytope.prod hP hQ

theorem IsPolytope.image {P : Set E} (hP : IsPolytope P) (f : E →ᵃ[ℝ] F) :
    IsPolytope (f '' P) :=
  IsVPolytope.image hP f

theorem IsPolytope.pi {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
    {P : ∀ i, Set (G i)} (hP : ∀ i, IsPolytope (P i)) :
    IsPolytope (Set.univ.pi P) := by
  classical
  choose S hS hPeq using hP
  refine ⟨Set.univ.pi S, Set.Finite.pi hS, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact mem_convexHull_pi fun i _ => hPeq i ▸ hx i trivial
  · refine convexHull_min (Set.pi_mono fun i _ => hPeq i ▸ subset_convexHull ℝ _) ?_
    exact convex_pi fun i _ => hPeq i ▸ convex_convexHull ℝ (S i)

theorem isHPolytope_empty : IsHPolytope (∅ : Set E) := by
  refine ⟨Bornology.isBounded_empty, {AffineMap.const ℝ E (1 : ℝ)}, finite_singleton _, ?_⟩
  ext x
  simp only [mem_empty_iff_false, mem_ofPred_eq, mem_singleton_iff, forall_eq,
    AffineMap.const_apply, false_iff, not_le]
  exact zero_lt_one

private lemma affineMap_eval_sum_smul (ℓ : E →ᵃ[ℝ] ℝ) {S : Finset E} {w : E → ℝ}
    (hw : ∑ v ∈ S, w v = 1) :
    ℓ (∑ v ∈ S, w v • v) = ∑ v ∈ S, w v * ℓ v := by
  have h : ℓ (S.affineCombination ℝ id w) = S.affineCombination ℝ (ℓ ∘ id) w :=
    Finset.map_affineCombination S id w hw ℓ
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hw, Function.comp_apply,
    id_eq, smul_eq_mul] using h

/-- Any finite or infinite intersection of closed affine half-spaces is convex. -/
theorem convex_setOf_forall_le (L : Set (E →ᵃ[ℝ] ℝ)) :
    Convex ℝ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} := by
  have heq : {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0} = ⋂ ℓ ∈ L, ℓ ⁻¹' Set.Iic (0 : ℝ) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [heq]
  exact convex_iInter fun ℓ => convex_iInter fun _ => (convex_Iic (0 : ℝ)).affine_preimage ℓ

/-- The intersection of two affine half-space systems is cut out by their union. -/
theorem setOf_forall_le_inter (L₁ L₂ : Set (E →ᵃ[ℝ] ℝ)) :
    {x : E | ∀ ℓ ∈ L₁, ℓ x ≤ 0} ∩ {x : E | ∀ ℓ ∈ L₂, ℓ x ≤ 0} =
      {x : E | ∀ ℓ ∈ L₁ ∪ L₂, ℓ x ≤ 0} := by
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_union, or_imp, forall_and]

private lemma preimage_setOf_forall_le (L : Set (F →ᵃ[ℝ] ℝ)) (f : E →ᵃ[ℝ] F) :
    f ⁻¹' {y : F | ∀ m ∈ L, m y ≤ 0} =
      {x : E | ∀ ℓ ∈ (fun m : F →ᵃ[ℝ] ℝ => m.comp f) '' L, ℓ x ≤ 0} := by
  ext x
  simp only [Set.mem_preimage, mem_ofPred_eq, Set.mem_image]
  exact ⟨fun h _ ⟨m, hm, hmeq⟩ => hmeq ▸ h m hm, fun h m hm => h (m.comp f) ⟨m, hm, rfl⟩⟩

private lemma prod_setOf_forall_le (L₁ : Set (E →ᵃ[ℝ] ℝ)) (L₂ : Set (F →ᵃ[ℝ] ℝ)) :
    {x : E | ∀ a ∈ L₁, a x ≤ 0} ×ˢ {y : F | ∀ b ∈ L₂, b y ≤ 0} =
      {p : E × F | ∀ ℓ ∈ (fun a : E →ᵃ[ℝ] ℝ => a.comp AffineMap.fst) '' L₁ ∪
        (fun b : F →ᵃ[ℝ] ℝ => b.comp AffineMap.snd) '' L₂, ℓ p ≤ 0} := by
  rw [show {x : E | ∀ a ∈ L₁, a x ≤ 0} ×ˢ {y : F | ∀ b ∈ L₂, b y ≤ 0} =
      (AffineMap.fst : E × F →ᵃ[ℝ] E) ⁻¹' {x | ∀ a ∈ L₁, a x ≤ 0} ∩
        (AffineMap.snd : E × F →ᵃ[ℝ] F) ⁻¹' {y | ∀ b ∈ L₂, b y ≤ 0} from rfl,
    preimage_setOf_forall_le L₁ (AffineMap.fst : E × F →ᵃ[ℝ] E),
    preimage_setOf_forall_le L₂ (AffineMap.snd : E × F →ᵃ[ℝ] F), setOf_forall_le_inter]

theorem IsHPolytope.convex {P : Set E} (hP : IsHPolytope P) : Convex ℝ P := by
  rcases hP with ⟨_, L, _, rfl⟩
  exact convex_setOf_forall_le L

theorem IsHPolytope.inter {P Q : Set E} (hP : IsHPolytope P) (hQ : IsHPolytope Q) :
    IsHPolytope (P ∩ Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨_, LQ, hLQ, rfl⟩
  exact ⟨hbP.subset inter_subset_left, LP ∪ LQ, hLP.union hLQ, setOf_forall_le_inter LP LQ⟩

theorem IsHPolytope.preimage_inter {P : Set E} {Q : Set F} (hP : IsHPolytope P)
    (hQ : IsHPolytope Q) (f : E →ᵃ[ℝ] F) : IsHPolytope (P ∩ f ⁻¹' Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨_, LQ, hLQ, rfl⟩
  exact ⟨hbP.subset inter_subset_left, LP ∪ (fun m : F →ᵃ[ℝ] ℝ => m.comp f) '' LQ,
    hLP.union (hLQ.image _), by rw [preimage_setOf_forall_le, setOf_forall_le_inter]⟩

theorem IsHPolytope.prod {P : Set E} {Q : Set F} (hP : IsHPolytope P) (hQ : IsHPolytope Q) :
    IsHPolytope (P ×ˢ Q) := by
  rcases hP with ⟨hbP, LP, hLP, rfl⟩
  rcases hQ with ⟨hbQ, LQ, hLQ, rfl⟩
  exact ⟨hbP.prod hbQ,
    (fun ℓ : E →ᵃ[ℝ] ℝ => ℓ.comp AffineMap.fst) '' LP ∪
      (fun m : F →ᵃ[ℝ] ℝ => m.comp AffineMap.snd) '' LQ,
    (hLP.image _).union (hLQ.image _), prod_setOf_forall_le LP LQ⟩

/-! ### Basic properties of faces -/

theorem IsPolytopeFace.subset {P F : Set E} (h : IsPolytopeFace P F) : F ⊆ P :=
  h.1.subset

theorem IsPolytopeFace.convex {P F : Set E} (h : IsPolytopeFace P F) : Convex ℝ F :=
  h.2

theorem IsPolytopeFace.isExtreme {P F : Set E} (h : IsPolytopeFace P F) : IsExtreme ℝ P F :=
  h.1

@[refl]
theorem IsPolytopeFace.refl {P : Set E} (hP : Convex ℝ P) : IsPolytopeFace P P :=
  ⟨IsExtreme.refl ℝ P, hP⟩

@[trans]
theorem IsPolytopeFace.trans {P Q R : Set E} (hPQ : IsPolytopeFace P Q) (hQR : IsPolytopeFace Q R) :
    IsPolytopeFace P R :=
  ⟨hPQ.1.trans hQR.1, hQR.2⟩

theorem IsPolytopeFace.inter {P F₁ F₂ : Set E} (h₁ : IsPolytopeFace P F₁)
    (h₂ : IsPolytopeFace P F₂) : IsPolytopeFace P (F₁ ∩ F₂) :=
  ⟨h₁.1.inter h₂.1, h₁.2.inter h₂.2⟩

theorem IsPolytopeFace.empty {P : Set E} : IsPolytopeFace P ∅ :=
  ⟨⟨empty_subset P, fun _ _ _ _ _ hz => False.elim hz⟩, convex_empty⟩

theorem IsPolytopeFace.mono {P Q R : Set E} (hPR : IsPolytopeFace P R) (hQP : Q ⊆ P)
    (hRQ : R ⊆ Q) : IsPolytopeFace Q R :=
  ⟨hPR.1.mono hQP hRQ, hPR.2⟩

theorem IsPolytopeFace.inter_inter {P₁ P₂ F₁ F₂ : Set E} (h₁ : IsPolytopeFace P₁ F₁)
    (h₂ : IsPolytopeFace P₂ F₂) : IsPolytopeFace (P₁ ∩ P₂) (F₁ ∩ F₂) := by
  refine ⟨⟨inter_subset_inter h₁.1.subset h₂.1.subset, fun x hx y hy z hz hzx => ?_⟩,
    h₁.2.inter h₂.2⟩
  exact ⟨h₁.1.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hzx,
    h₂.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 hzx⟩

theorem IsPolytopeFace.prod {P₁ : Set E} {P₂ : Set F} {F₁ : Set E} {F₂ : Set F}
    (h₁ : IsPolytopeFace P₁ F₁) (h₂ : IsPolytopeFace P₂ F₂) :
    IsPolytopeFace (P₁ ×ˢ P₂) (F₁ ×ˢ F₂) := by
  refine ⟨⟨prod_mono h₁.1.subset h₂.1.subset, fun x hx y hy z hz hzx => ?_⟩, h₁.2.prod h₂.2⟩
  rcases hzx with ⟨a, b, ha, hb, hab, rfl⟩
  exact ⟨h₁.1.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 ⟨a, b, ha, hb, hab, rfl⟩,
    h₂.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 ⟨a, b, ha, hb, hab, rfl⟩⟩

theorem IsPolytopeFace.preimage {P : Set E} {Q G : Set F} (hP : Convex ℝ P) (f : E →ᵃ[ℝ] F)
    (h : IsPolytopeFace Q G) : IsPolytopeFace (P ∩ f ⁻¹' Q) (P ∩ f ⁻¹' G) := by
  refine ⟨⟨inter_subset_inter_right P (preimage_mono h.1.subset),
    fun x hx y hy z hz hzx => ?_⟩, hP.inter (h.2.affine_preimage f)⟩
  refine ⟨hx.1, h.1.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 ?_⟩
  have hmem : f z ∈ f '' openSegment ℝ x y := mem_image_of_mem f hzx
  rwa [image_openSegment _ f] at hmem

theorem IsPolytopeFace.left_mem_of_smul_add_mem {P F : Set E} (hPF : IsPolytopeFace P F)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {a y : E} (ha : a ∈ P) (hy : y ∈ P)
    (hmem : c • a + (1 - c) • y ∈ F) : a ∈ F := by
  rcases eq_or_lt_of_le hc1 with rfl | hlt
  · simpa only [one_smul, sub_self, zero_smul, add_zero] using hmem
  · exact hPF.isExtreme.left_mem_of_mem_openSegment ha hy hmem
      ⟨c, 1 - c, hc0, sub_pos.2 hlt, add_sub_cancel c 1, rfl⟩

end BasicDefs

section FiniteDim

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
private lemma affineMap_lineMap (ℓ : E →ᵃ[ℝ] ℝ) (x y : E) (t : ℝ) :
    ℓ (AffineMap.lineMap x y t) = ℓ x + t * (ℓ y - ℓ x) := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  ring

theorem IsHPolytope.isClosed {P : Set E} (hP : IsHPolytope P) : IsClosed P := by
  rcases hP with ⟨_, L, _, rfl⟩
  simp only [Set.ofPred_forall]
  exact isClosed_biInter fun ℓ _ => isClosed_le ℓ.continuous_of_finiteDimensional continuous_const

theorem IsHPolytope.isCompact {P : Set E} (hP : IsHPolytope P) : IsCompact P :=
  Metric.isCompact_of_isClosed_isBounded hP.isClosed hP.1

omit [FiniteDimensional ℝ E] in
/-- Moving from `x` along the line through `y` preserves finitely many affine inequalities `ℓ ≤ 0`
for all sufficiently small `|t|`, provided every inequality active at `x` also vanishes at `y`. -/
private lemma exists_lineMap_mem_setOf_le {L : Set (E →ᵃ[ℝ] ℝ)} (hL : L.Finite)
    {x y : E} (hx : ∀ ℓ ∈ L, ℓ x ≤ 0) (heq : ∀ ℓ ∈ L, ℓ x = 0 → ℓ y = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → ∀ ℓ ∈ L, ℓ (AffineMap.lineMap x y t) ≤ 0 := by
  classical
  set strict : Finset (E →ᵃ[ℝ] ℝ) := hL.toFinset.filter (fun ℓ => ℓ x < 0)
  let bound : (E →ᵃ[ℝ] ℝ) → ℝ := fun ℓ => (-ℓ x) / (|ℓ y - ℓ x| + 1)
  let ε : ℝ := if hs : strict.Nonempty then min 1 (strict.inf' hs bound) else 1
  have hε_pos : 0 < ε := by
    by_cases hs : strict.Nonempty
    · simp only [ε, dite_eq_left hs, lt_min_iff]
      exact ⟨one_pos, (Finset.lt_inf'_iff hs).2 fun ℓ hℓ =>
        div_pos (neg_pos.2 (Finset.mem_filter.1 hℓ).2) (by positivity)⟩
    · simp only [ε, dite_eq_right hs]; exact one_pos
  refine ⟨ε, hε_pos, fun t ht ℓ hℓ => ?_⟩
  rw [affineMap_lineMap]
  rcases (hx ℓ hℓ).lt_or_eq with hlt | hx0
  · have hstrict : ℓ ∈ strict := Finset.mem_filter.2 ⟨hL.mem_toFinset.2 hℓ, hlt⟩
    have hs : strict.Nonempty := ⟨ℓ, hstrict⟩
    have hε_le : ε ≤ bound ℓ := by
      dsimp only [ε]; rw [dite_eq_left hs]
      exact (min_le_right 1 _).trans (Finset.inf'_le bound hstrict)
    have h1 : |t| * (|ℓ y - ℓ x| + 1) ≤ -ℓ x :=
      (mul_le_mul_of_nonneg_right (ht.trans hε_le) (by positivity)).trans_eq
        (div_mul_cancel₀ _ (by positivity))
    linarith [abs_nonneg t, (le_abs_self (t * (ℓ y - ℓ x))).trans_eq (abs_mul _ _)]
  · rw [hx0, heq ℓ hℓ hx0, sub_zero, mul_zero, add_zero]

omit [FiniteDimensional ℝ E] in
private lemma finite_extremePoints_of_isHPolytope {P : Set E} (hP : IsHPolytope P) :
    (P.extremePoints ℝ).Finite := by
  classical
  rcases hP with ⟨_, L, hL, rfl⟩
  let active : E → Finset (E →ᵃ[ℝ] ℝ) := fun x => hL.toFinset.filter (fun ℓ => ℓ x = 0)
  have hmaps : MapsTo active (Set.extremePoints ℝ {x : E | ∀ ℓ ∈ L, ℓ x ≤ 0})
      (hL.toFinset.powerset : Set (Finset (E →ᵃ[ℝ] ℝ))) :=
    fun _ _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  refine (Finset.finite_toSet hL.toFinset.powerset).of_injOn hmaps fun x hx y _ hxy => ?_
  by_contra hne
  obtain ⟨ε, hε_pos, hmem⟩ := exists_lineMap_mem_setOf_le hL (x := x) (y := y) hx.1
    fun ℓ hℓ hx0 => by
      have ha : ℓ ∈ active y := hxy ▸ show ℓ ∈ active x from
        Finset.mem_filter.2 ⟨hL.mem_toFinset.2 hℓ, hx0⟩
      exact (Finset.mem_filter.1 ha).2
  have hx₁ := hmem (-ε) (by rw [abs_neg, abs_of_pos hε_pos])
  have hx₂ := hmem ε (by rw [abs_of_pos hε_pos])
  have hmid : x ∈ openSegment ℝ (AffineMap.lineMap x y (-ε)) (AffineMap.lineMap x y ε) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
      by simp only [AffineMap.lineMap_apply_module]; module⟩
  have heq₁ := ((mem_extremePoints.1 hx).2 _ hx₁ _ hx₂ hmid).1
  have hdiff : (-ε) • (y - x) = 0 := by
    rw [← sub_eq_zero.2 heq₁, AffineMap.lineMap_apply_module]; module
  exact hne (sub_eq_zero.1 ((smul_eq_zero.1 hdiff).resolve_left (by linarith))).symm

/-- Every bounded H-polytope is the convex hull of its finite set of extreme points, hence a
V-polytope. -/
theorem IsHPolytope.eq_convexHull_extremePoints {P : Set E} (hP : IsHPolytope P) :
    P = convexHull ℝ (P.extremePoints ℝ) := by
  have hkm := closure_convexHull_extremePoints hP.isCompact hP.convex
  rwa [((finite_extremePoints_of_isHPolytope hP).isClosed_convexHull ℝ).closure_eq,
    eq_comm] at hkm

theorem IsHPolytope.isVPolytope {P : Set E} (hP : IsHPolytope P) : IsVPolytope P :=
  ⟨P.extremePoints ℝ, finite_extremePoints_of_isHPolytope hP, hP.eq_convexHull_extremePoints⟩

omit [FiniteDimensional ℝ E] in
private lemma mem_convexHull_iff_coords {d m : ℕ} (eE : E ≃ₗ[ℝ] (Fin d → ℝ))
    {Sf : Finset E} (eS : Fin m ≃ Sf) (x : E) :
    x ∈ convexHull ℝ (Sf : Set E) ↔
      ∃ w : Fin m → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        ∀ k : Fin d, ∑ j, w j * eE (eS j).1 k = eE x k := by
  classical
  rw [Finset.mem_convexHull']
  constructor
  · rintro ⟨w', hw'₀, hw'₁, rfl⟩
    refine ⟨fun j => w' (eS j).1, fun j => hw'₀ _ (eS j).2, ?_, fun k => ?_⟩
    · exact (Fintype.sum_equiv eS _ (fun u : Sf => w' u.1) fun _ => rfl).trans
        ((Finset.sum_coe_sort Sf w').trans hw'₁)
    · rw [map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
      exact (Fintype.sum_equiv eS _ (fun u : Sf => w' u.1 * eE u.1 k) fun _ => rfl).trans
        (Finset.sum_coe_sort Sf (fun u => w' u * eE u k))
  · rintro ⟨w, hw₀, hw₁, hVk⟩
    let w' : E → ℝ := fun u => if hu : u ∈ Sf then w (eS.symm ⟨u, hu⟩) else 0
    have hw'sum : ∑ u ∈ Sf, w' u = 1 := by
      rw [← Finset.sum_coe_sort Sf w']
      exact (Fintype.sum_equiv eS.symm (fun u : Sf => w' u.1) w fun u => by
        simp only [w', dite_eq_left u.2]).trans hw₁
    refine ⟨w', fun u hu => by simp only [w', dite_eq_left hu]; exact hw₀ _, hw'sum,
      eE.injective <| funext fun k => ?_⟩
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, ← hVk k]
    rw [← Finset.sum_coe_sort Sf (fun u => w' u * eE u k)]
    exact Fintype.sum_equiv eS.symm (fun u : Sf => w' u.1 * eE u.1 k)
      (fun j => w j * eE (eS j).1 k) fun u => by
        simp only [w', dite_eq_left u.2, Equiv.apply_symm_apply]

private lemma fourierMotzkin_convexHull_system {d m : ℕ} (V : Fin m → Fin d → ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (A : Matrix ι (Fin m) ℝ) (B : Matrix ι (Fin d) ℝ)
      (rhs : ι → ℝ), ∀ (z : Fin d → ℝ) (w : Fin m → ℝ),
        (A *ᵥ w + B *ᵥ z ≤ rhs) ↔
          (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∀ k, ∑ j, w j * V j k = z k := by
  let ι := (Fin d ⊕ Fin d) ⊕ (Unit ⊕ Unit) ⊕ Fin m
  let A : Matrix ι (Fin m) ℝ := Matrix.of fun r j => match r with
    | .inl (.inl k) => -V j k
    | .inl (.inr k) => V j k
    | .inr (.inl (.inl ())) => 1
    | .inr (.inl (.inr ())) => -1
    | .inr (.inr j₀) => if j = j₀ then -1 else 0
  let B : Matrix ι (Fin d) ℝ := Matrix.of fun r k => match r with
    | .inl (.inl k₀) => if k = k₀ then 1 else 0
    | .inl (.inr k₀) => if k = k₀ then -1 else 0
    | .inr _ => 0
  let rhs : ι → ℝ := fun r => match r with
    | .inr (.inl (.inl ())) => 1
    | .inr (.inl (.inr ())) => -1
    | _ => 0
  refine ⟨ι, inferInstance, A, B, rhs, fun z w => ?_⟩
  have hcomm : ∀ k, ∑ j, V j k * w j = ∑ j, w j * V j k :=
    fun k => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [ι, Pi.le_def, Sum.forall, Unique.forall_iff, Pi.add_apply, Matrix.mulVec,
    dotProduct, A, B, rhs, Matrix.of_apply, ite_mul, neg_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, add_zero,
    Finset.sum_neg_distrib, neg_nonpos, neg_le_neg_iff]
  refine ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ => ⟨h5, le_antisymm h3 h4, fun k =>
    le_antisymm (by linarith [h2 k, hcomm k]) (by linarith [h1 k, hcomm k])⟩,
    fun ⟨hw₀, hw₁, hVk⟩ => ⟨⟨fun k => by linarith [hVk k, hcomm k],
      fun k => by linarith [hVk k, hcomm k]⟩, ⟨hw₁.le, hw₁.ge⟩, hw₀⟩⟩

theorem IsVPolytope.isHPolytope {P : Set E} (hP : IsVPolytope P) : IsHPolytope P := by
  classical
  rcases hP with ⟨S, hS, rfl⟩
  by_cases hSne : S.Nonempty
  · refine ⟨(hS.isCompact_convexHull ℝ).isBounded, ?_⟩
    let eE := (Module.finBasis ℝ E).equivFun
    let Sf := hS.toFinset
    let eS := (Fintype.equivFin Sf).symm
    obtain ⟨ι, _, A, B, rhs, hsys⟩ := fourierMotzkin_convexHull_system fun j => eE (eS j).1
    obtain ⟨ρ, _, T, _, _, hproj⟩ := Matrix.FourierMotzkin.exists_projection A B rhs
    let ℓ : ρ → E →ᵃ[ℝ] ℝ := fun r =>
      (LinearMap.proj r ∘ₗ (T * B).mulVecLin ∘ₗ eE.toLinearMap).toAffineMap -
        AffineMap.const ℝ E ((T *ᵥ rhs) r)
    refine ⟨Set.range ℓ, Set.finite_range ℓ, ?_⟩
    ext x
    rw [← hS.coe_toFinset, mem_convexHull_iff_coords eE eS]
    simp only [mem_ofPred_eq, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, ℓ,
      FunLike.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply, LinearMap.coe_proj,
      Function.eval, AffineMap.const_apply, sub_nonpos]
    exact ⟨fun ⟨w, hw⟩ => (hproj (eE x)).1 ⟨w, (hsys (eE x) w).2 hw⟩,
      fun hle => let ⟨w, hw⟩ := (hproj (eE x)).2 hle; ⟨w, (hsys (eE x) w).1 hw⟩⟩
  · rw [not_nonempty_iff_eq_empty.1 hSne, convexHull_empty]
    exact isHPolytope_empty

/-- **Weyl–Minkowski theorem** for compact convex polytopes: a set is the convex hull of finitely
many points if and only if it is a bounded intersection of finitely many closed half-spaces. -/
theorem isHPolytope_iff_isVPolytope {P : Set E} : IsHPolytope P ↔ IsVPolytope P :=
  ⟨IsHPolytope.isVPolytope, IsVPolytope.isHPolytope⟩

theorem isPolytope_iff_isHPolytope {P : Set E} : IsPolytope P ↔ IsHPolytope P :=
  isHPolytope_iff_isVPolytope.symm

theorem IsPolytope.finite_extremePoints {P : Set E} (hP : IsPolytope P) :
    (P.extremePoints ℝ).Finite :=
  finite_extremePoints_of_isHPolytope (isPolytope_iff_isHPolytope.1 hP)

theorem IsPolytope.eq_convexHull_extremePoints {P : Set E} (hP : IsPolytope P) :
    P = convexHull ℝ (P.extremePoints ℝ) :=
  (isPolytope_iff_isHPolytope.1 hP).eq_convexHull_extremePoints

theorem IsPolytope.inter {P Q : Set E} (hP : IsPolytope P) (hQ : IsPolytope Q) :
    IsPolytope (P ∩ Q) :=
  ((isPolytope_iff_isHPolytope.1 hP).inter (isPolytope_iff_isHPolytope.1 hQ)).isVPolytope

theorem IsPolytope.preimage_inter {P : Set E} {Q : Set F} (hP : IsPolytope P)
    (hQ : IsPolytope Q) (f : E →ᵃ[ℝ] F) : IsPolytope (P ∩ f ⁻¹' Q) :=
  ((isPolytope_iff_isHPolytope.1 hP).preimage_inter
    (isPolytope_iff_isHPolytope.1 hQ) f).isVPolytope

theorem IsPolytope.inter_setOf_le {P : Set E} (hP : IsPolytope P) {L : Set (E →ᵃ[ℝ] ℝ)}
    (hL : L.Finite) : IsPolytope (P ∩ {x | ∀ ℓ ∈ L, ℓ x ≤ 0}) := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  exact IsHPolytope.isVPolytope
    ⟨hP.isBounded.subset inter_subset_left, LP ∪ L, hLP.union hL,
      by rw [hPeq, setOf_forall_le_inter]⟩

/-! ### Faces and vertex centroids of polytopes -/

omit [FiniteDimensional ℝ E] in
theorem isExtreme_mem_of_sum_pos {P F : Set E} (hPF : IsExtreme ℝ P F) (hP : Convex ℝ P)
    {S : Finset E} (hSne : S.Nonempty) (hSP : (S : Set E) ⊆ P) (w : E → ℝ)
    (hwpos : ∀ v ∈ S, 0 < w v) (hwsum : ∑ v ∈ S, w v = 1) (hxF : (∑ v ∈ S, w v • v) ∈ F) :
    ∀ v ∈ S, v ∈ F := by
  classical
  have _ := hSne
  intro a ha
  rcases (S.erase a).eq_empty_or_nonempty with hmt | hne
  · have hwa : w a = 1 := by
      have h := Finset.add_sum_erase S w ha; rwa [hmt, Finset.sum_empty, add_zero, hwsum] at h
    have hsum := Finset.add_sum_erase S (fun v => w v • v) ha
    rw [hmt, Finset.sum_empty, add_zero, hwa, one_smul] at hsum
    exact hsum ▸ hxF
  · have hr_eq : ∑ v ∈ S.erase a, w v = 1 - w a := by
      linarith [Finset.add_sum_erase S w ha]
    have hr_pos : 0 < 1 - w a :=
      hr_eq ▸ Finset.sum_pos (fun v hv => hwpos v (Finset.erase_subset a S hv)) hne
    have hy_sum : ∑ v ∈ S.erase a, w v / (1 - w a) = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, hr_eq, mul_inv_cancel₀ hr_pos.ne']
    have hyP : ∑ v ∈ S.erase a, (w v / (1 - w a)) • v ∈ P := hP.sum_mem
      (fun v hv => div_nonneg (hwpos v (Finset.erase_subset a S hv)).le hr_pos.le)
      hy_sum (fun v hv => hSP (Finset.erase_subset a S hv))
    have hxy : w a • a + (1 - w a) • ∑ v ∈ S.erase a, (w v / (1 - w a)) • v =
        ∑ v ∈ S, w v • v := by
      rw [← Finset.add_sum_erase S (fun v => w v • v) ha, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun v _ => by rw [smul_smul, mul_div_cancel₀ _ hr_pos.ne']
    exact hPF.left_mem_of_mem_openSegment (hSP ha) hyP hxF
      ⟨w a, 1 - w a, hwpos a ha, hr_pos, by ring, hxy⟩

omit [FiniteDimensional ℝ E] in
/-- Any point in `convexHull ℝ (s : Set E) ∩ R`, where `(s : Set E) ⊆ Q` and `R` is extreme in
convex `Q`, lies in the convex hull of a nonempty subset `t ⊆ s` contained in `R`. -/
theorem exists_finset_subset_convexHull_of_isExtreme {s : Finset E} {Q R : Set E}
    (hQ : Convex ℝ Q) (hsQ : (s : Set E) ⊆ Q) (hQR : IsExtreme ℝ Q R)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E) ∩ R) :
    ∃ t ⊆ s, t.Nonempty ∧ (t : Set E) ⊆ R ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx.1
  let t := s.filter (fun v => 0 < w v)
  have hwt0 : ∀ v ∈ s, v ∉ t → w v = 0 := fun v hv hn => by
    simp only [t, Finset.mem_filter, not_and, not_lt] at hn
    exact le_antisymm (hn hv) (hw0 v hv)
  have hw_pos : ∀ v ∈ t, 0 < w v := fun v hv => (Finset.mem_filter.1 hv).2
  have hw_sum : ∑ v ∈ t, w v = 1 :=
    (Finset.sum_subset (Finset.filter_subset _ s) hwt0).trans hw1
  have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 fun hmt => by simp [hmt] at hw_sum
  have hx_comb : ∑ v ∈ t, w v • v = x := by
    rw [← hwx]
    exact Finset.sum_subset (Finset.filter_subset _ s) fun v hv hn => by
      rw [hwt0 v hv hn, zero_smul]
  have htR := isExtreme_mem_of_sum_pos hQR hQ htne
    (Subset.trans (Finset.coe_subset.2 (Finset.filter_subset _ s)) hsQ)
    w hw_pos hw_sum (hx_comb.symm ▸ hx.2)
  exact ⟨t, Finset.filter_subset _ s, htne, fun v hv => htR v hv,
    Finset.mem_convexHull'.2 ⟨w, fun v hv => (hw_pos v hv).le, hw_sum, hx_comb⟩⟩

theorem IsPolytopeFace.eq_convexHull_extremePoints_inter {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) : F = convexHull ℝ (P.extremePoints ℝ ∩ F) := by
  classical
  refine Subset.antisymm (fun x hx => ?_) (convexHull_min inter_subset_right hPF.convex)
  have hVfin := hP.finite_extremePoints
  set V : Finset E := hVfin.toFinset
  have hxV : x ∈ convexHull ℝ (V : Set E) := by
    rw [hVfin.coe_toFinset, ← hP.eq_convexHull_extremePoints]
    exact hPF.subset hx
  have hVP : (V : Set E) ⊆ P := fun _ hv => (hVfin.mem_toFinset.1 hv).1
  obtain ⟨S, hSV, _, hSF, hxS⟩ :=
    exists_finset_subset_convexHull_of_isExtreme hP.convex hVP hPF.isExtreme ⟨hxV, hx⟩
  refine convexHull_mono ?_ hxS
  exact fun v hv => ⟨hVfin.mem_toFinset.1 (hSV hv), hSF hv⟩

theorem IsPolytopeFace.isPolytope {P F : Set E} (hP : IsPolytope P) (hPF : IsPolytopeFace P F) :
    IsPolytope F :=
  ⟨P.extremePoints ℝ ∩ F, hP.finite_extremePoints.subset inter_subset_left,
    hPF.eq_convexHull_extremePoints_inter hP⟩

omit [FiniteDimensional ℝ E] in
theorem IsPolytopeFace.extremePoints_eq {P F : Set E} (hPF : IsPolytopeFace P F) :
    F.extremePoints ℝ = P.extremePoints ℝ ∩ F := by
  rw [hPF.isExtreme.extremePoints_eq, inter_comm]

theorem IsPolytope.extremePoints_nonempty {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty) :
    (P.extremePoints ℝ).Nonempty :=
  convexHull_nonempty_iff.1 (by rwa [← hP.eq_convexHull_extremePoints])

theorem vertexCentroid_eq_centroid {P : Set E} (hP : IsPolytope P) :
    vertexCentroid P = hP.finite_extremePoints.toFinset.centroid ℝ id := by
  unfold vertexCentroid
  rw [dite_eq_left hP.finite_extremePoints]

theorem vertexCentroid_mem {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty) :
    vertexCentroid P ∈ P := by
  have hmem := Finset.centroid_mem_convexHull (R := ℝ) _
    (hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne))
  rwa [hP.finite_extremePoints.coe_toFinset, ← hP.eq_convexHull_extremePoints,
    ← vertexCentroid_eq_centroid hP] at hmem

private lemma vertexCentroid_eq_sum {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty) :
    vertexCentroid P =
      ∑ v ∈ hP.finite_extremePoints.toFinset,
        hP.finite_extremePoints.toFinset.centroidWeights ℝ v • v := by
  have hVne := hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne)
  rw [vertexCentroid_eq_centroid hP, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)]
  rfl

theorem vertexCentroid_notMem_of_ssubset {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hss : F ⊂ P) : vertexCentroid P ∉ F := by
  intro hbF
  have hne : P.Nonempty := ⟨vertexCentroid P, hPF.subset hbF⟩
  set V := hP.finite_extremePoints.toFinset
  have hVne : V.Nonempty :=
    hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne)
  have hVF : (V : Set E) ⊆ F := isExtreme_mem_of_sum_pos hPF.isExtreme hP.convex hVne
    (fun _ hv => (hP.finite_extremePoints.mem_toFinset.1 hv).1) (V.centroidWeights ℝ)
    (fun _ _ => by simpa using Finset.card_pos.2 hVne)
    (Finset.sum_centroidWeights_eq_one_of_nonempty _ _ hVne)
    (vertexCentroid_eq_sum hP hne ▸ hbF)
  exact hss.not_subset (by
    rw [hP.eq_convexHull_extremePoints, ← hP.finite_extremePoints.coe_toFinset]
    exact convexHull_min hVF hPF.convex)

omit [FiniteDimensional ℝ E] in
private lemma mem_affineSpan_finset_iff_sum {V : Finset E} {x : E}
    (hx : x ∈ affineSpan ℝ (V : Set E)) :
    ∃ w : E → ℝ, ∑ v ∈ V, w v = 1 ∧ x = ∑ v ∈ V, w v • v := by
  classical
  have hx' : x ∈ affineSpan ℝ (Set.range ((↑) : V → E)) := by
    rwa [Subtype.range_coe_subtype]
  rw [mem_affineSpan_iff_eq_affineCombination] at hx'
  obtain ⟨s', w', hw'1, rfl⟩ := hx'
  refine ⟨fun v => if hv : v ∈ V then if ⟨v, hv⟩ ∈ s' then w' ⟨v, hv⟩ else 0 else 0, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort V, ← Finset.sum_subset (Finset.subset_univ s') fun v _ hns => by
      simp only [v.2, hns, ↓reduceDIte, ↓reduceIte]]
    exact (Finset.sum_congr rfl fun v hv => by
      simp only [v.2, hv, ↓reduceDIte, ↓reduceIte]).trans hw'1
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw'1, ← Finset.sum_coe_sort V,
      ← Finset.sum_subset (Finset.subset_univ s') fun v _ hns => by
        simp only [v.2, hns, ↓reduceDIte, ↓reduceIte, zero_smul]]
    exact Finset.sum_congr rfl fun v hv => by simp only [v.2, hv, ↓reduceDIte, ↓reduceIte]

theorem IsPolytopeFace.inter_affineSpan_eq {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hne : F.Nonempty) : P ∩ (affineSpan ℝ F : Set E) = F := by
  classical
  refine Subset.antisymm ?_ (subset_inter hPF.subset (subset_affineSpan ℝ F))
  intro x ⟨hxP, hxaff⟩
  have hFp := hPF.isPolytope hP
  set V : Finset E := hFp.finite_extremePoints.toFinset
  have hVne : V.Nonempty :=
    hFp.finite_extremePoints.toFinset_nonempty.2 (hFp.extremePoints_nonempty hne)
  obtain ⟨w, hw1, rfl⟩ := mem_affineSpan_finset_iff_sum (by
    rwa [← affineSpan_convexHull (V : Set E), hFp.finite_extremePoints.coe_toFinset,
      ← hFp.eq_convexHull_extremePoints])
  let n : ℝ := V.card
  let M : ℝ := ∑ v ∈ V, |w v|
  have hn1 : 1 ≤ n := Nat.one_le_cast.2 (Finset.card_pos.2 hVne)
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hden_pos : 0 < 2 * n * (M + 1) := by positivity
  let ε : ℝ := 1 / (2 * n * (M + 1))
  have hε_pos : 0 < ε := div_pos one_pos hden_pos
  have hε_le : ε ≤ 1 / 2 := (div_le_div_iff₀ hden_pos two_pos).2 (by nlinarith)
  let u : E → ℝ := fun v => (1 - ε) * (1 / n) + ε * w v
  have husum : ∑ v ∈ V, u v = 1 := by
    simp only [u, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hw1]
    have hn0 : n ≠ 0 := by linarith
    field_simp; ring
  have hu0 : ∀ v ∈ V, 0 ≤ u v := fun v hv => by
    have hlo : -M ≤ w v := by
      linarith [neg_abs_le (w v), Finset.single_le_sum (fun z _ => abs_nonneg (w z)) hv]
    have hprod : ε * M ≤ 1 / (2 * n) := by
      rw [show ε * M = M / (2 * n * (M + 1)) by dsimp only [ε]; ring,
        div_le_div_iff₀ hden_pos (by positivity)]; nlinarith
    linarith [mul_le_mul_of_nonneg_left hlo hε_pos.le,
      show 1 / (2 * n) ≤ (1 - ε) * (1 / n) by
        nlinarith [show (0 : ℝ) < 1 / n by positivity, show 1 / 2 * (1 / n) = 1 / (2 * n) by ring]]
  have hyF : (1 - ε) • vertexCentroid F + ε • ∑ v ∈ V, w v • v ∈ F := by
    rw [show (1 - ε) • vertexCentroid F + ε • ∑ v ∈ V, w v • v = ∑ v ∈ V, u v • v by
      rw [show vertexCentroid F = ∑ v ∈ V, (1 / n) • v by
        simpa only [Finset.centroidWeights_apply, one_div] using vertexCentroid_eq_sum hFp hne,
        Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by rw [smul_smul, smul_smul, ← add_smul]]
    exact hPF.convex.sum_mem hu0 husum fun _ hv => (hFp.finite_extremePoints.mem_toFinset.1 hv).1
  exact hPF.isExtreme.right_mem_of_mem_openSegment (hPF.subset (vertexCentroid_mem hFp hne)) hxP
    hyF ⟨1 - ε, ε, by linarith, hε_pos, sub_add_cancel 1 ε, rfl⟩

theorem vertexCentroid_notMem_affineSpan_of_ssubset {P F : Set E} (hP : IsPolytope P)
    (hPF : IsPolytopeFace P F) (hne : F.Nonempty) (hss : F ⊂ P) :
    vertexCentroid P ∉ affineSpan ℝ F := fun hmem =>
  vertexCentroid_notMem_of_ssubset hP hPF hss <|
    hPF.inter_affineSpan_eq hP hne ▸
      ⟨vertexCentroid_mem hP ⟨hne.some, hPF.subset hne.some_mem⟩, hmem⟩

theorem IsPolytope.apply_vertexCentroid_lt {P : Set E} (hP : IsPolytope P) (hne : P.Nonempty)
    {ℓ : E →ᵃ[ℝ] ℝ} (hℓ_le : ∀ z ∈ P, ℓ z ≤ 0) {y : E} (hyP : y ∈ P) (hylt : ℓ y < 0) :
    ℓ (vertexCentroid P) < 0 := by
  classical
  set V : Finset E := hP.finite_extremePoints.toFinset
  have hVne := hP.finite_extremePoints.toFinset_nonempty.2 (hP.extremePoints_nonempty hne)
  have hVsub : (V : Set E) ⊆ P := fun _ hv => (hP.finite_extremePoints.mem_toFinset.1 hv).1
  obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1
    (by rwa [hP.finite_extremePoints.coe_toFinset, ← hP.eq_convexHull_extremePoints] :
      y ∈ convexHull ℝ (V : Set E))
  rw [affineMap_eval_sum_smul ℓ hw1] at hylt
  obtain ⟨v₀, hv₀, hv₀lt⟩ : ∃ v₀ ∈ V, ℓ v₀ < 0 := by
    by_contra! hge
    linarith [Finset.sum_nonneg fun v hv => mul_nonneg (hw0 v hv) (hge v hv)]
  rw [vertexCentroid_eq_sum hP hne,
    affineMap_eval_sum_smul ℓ (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ V hVne),
    ← Finset.add_sum_erase _ _ hv₀]
  have hhead : V.centroidWeights ℝ v₀ * ℓ v₀ < 0 := mul_neg_of_pos_of_neg (by
    simp only [Finset.centroidWeights_apply, inv_pos, Nat.cast_pos]
    exact Finset.card_pos.2 hVne) hv₀lt
  have hrest : ∑ v ∈ V.erase v₀, V.centroidWeights ℝ v * ℓ v ≤ 0 :=
    Finset.sum_nonpos fun v hv => mul_nonpos_of_nonneg_of_nonpos
      (by simp [Finset.centroidWeights_apply]) (hℓ_le v (hVsub (Finset.mem_of_mem_erase hv)))
  linarith

private lemma isExposed_of_eq_zero {R : Set E} {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite)
    (hReq : R = {x | ∀ ℓ ∈ LR, ℓ x ≤ 0}) {L₀ : Set (E →ᵃ[ℝ] ℝ)} (hL₀ : L₀ ⊆ LR) :
    IsExposed ℝ R {x ∈ R | ∀ ℓ ∈ L₀, ℓ x = 0} := by
  classical
  set L₀f : Finset (E →ᵃ[ℝ] ℝ) := (hLR.subset hL₀).toFinset
  let gLin : E →ₗ[ℝ] ℝ := ∑ ℓ ∈ L₀f, ℓ.linear
  let g : StrongDual ℝ E := ⟨gLin, gLin.continuous_of_finiteDimensional⟩
  have hdiff : ∀ u v : E, g u - g v = ∑ ℓ ∈ L₀f, (ℓ u - ℓ v) := fun u v => by
    simp only [g, gLin, ContinuousLinearMap.coe_mk', LinearMap.coe_sum, Finset.sum_apply,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by
      rw [← map_sub, ← vsub_eq_sub, ℓ.linear_apply_vsub, vsub_eq_sub]
  intro hne
  refine ⟨g, Subset.antisymm (fun x hx => ⟨hx.1, fun y hy => ?_⟩) fun x ⟨hxR, hxmax⟩ => ?_⟩
  · have hnp : g y - g x ≤ 0 := hdiff y x ▸ Finset.sum_nonpos fun ℓ hℓ => by
      have hℓ₀ := (hLR.subset hL₀).mem_toFinset.1 hℓ
      rw [hx.2 ℓ hℓ₀, sub_zero]; exact (hReq ▸ hy) ℓ (hL₀ hℓ₀)
    linarith
  · obtain ⟨y₀, hy₀⟩ := hne
    have hnonneg : ∀ m ∈ L₀f, 0 ≤ -m x := fun m hm =>
      neg_nonneg.2 ((hReq ▸ hxR) m (hL₀ ((hLR.subset hL₀).mem_toFinset.1 hm)))
    have hsum : ∑ m ∈ L₀f, (-m x) ≤ 0 := by
      have hsub : g y₀ - g x = ∑ m ∈ L₀f, (-m x) := (hdiff y₀ x).trans
        (Finset.sum_congr rfl fun m hm => by
          rw [hy₀.2 m ((hLR.subset hL₀).mem_toFinset.1 hm), zero_sub])
      linarith [hxmax y₀ hy₀.1]
    exact ⟨hxR, fun ℓ hℓ => neg_eq_zero.1 <| (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1
      (le_antisymm hsum (Finset.sum_nonneg hnonneg)) ℓ ((hLR.subset hL₀).mem_toFinset.2 hℓ)⟩

omit [FiniteDimensional ℝ E] in
theorem IsExposed.isPolytopeFace {P F : Set E} (hP : Convex ℝ P) (hPF : IsExposed ℝ P F) :
    IsPolytopeFace P F := by
  refine ⟨hPF.isExtreme, ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact convex_empty
  · obtain ⟨l, rfl⟩ := hPF hne
    intro x hx y hy a b ha hb hab
    refine ⟨hP hx.1 hy.1 ha hb hab, fun z hz => ?_⟩
    simp only [smul_eq_mul, map_add, map_smul]
    have hax : a * l z ≤ a * l x := mul_le_mul_of_nonneg_left (hx.2 z hz) ha
    have hby : b * l z ≤ b * l y := mul_le_mul_of_nonneg_left (hy.2 z hz) hb
    linarith [show a * l z + b * l z = l z by rw [← add_mul, hab, one_mul]]

theorem isPolytopeFace_of_eq_zero {R : Set E} {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite)
    (hReq : R = {x | ∀ ℓ ∈ LR, ℓ x ≤ 0}) (hRc : Convex ℝ R)
    {L₀ : Set (E →ᵃ[ℝ] ℝ)} (hL₀ : L₀ ⊆ LR) :
    IsPolytopeFace R {x ∈ R | ∀ ℓ ∈ L₀, ℓ x = 0} :=
  IsExposed.isPolytopeFace hRc (isExposed_of_eq_zero hLR hReq hL₀)

theorem IsPolytopeFace.exists_eq_zero_of_isHPolytope {P F : Set E}
    {L : Set (E →ᵃ[ℝ] ℝ)} (hL : L.Finite) (hPL : P = {x | ∀ ℓ ∈ L, ℓ x ≤ 0})
    (hP : IsPolytope P) (hPF : IsPolytopeFace P F) (hne : F.Nonempty) :
    ∃ L₀ ⊆ L, F = {x ∈ P | ∀ ℓ ∈ L₀, ℓ x = 0} := by
  let L₀ : Set (E →ᵃ[ℝ] ℝ) := {ℓ ∈ L | ∀ y ∈ F, ℓ y = 0}
  refine ⟨L₀, fun _ h => h.1,
    Subset.antisymm (fun x hx => ⟨hPF.subset hx, fun _ hℓ => hℓ.2 x hx⟩) fun z ⟨hzP, hzL₀⟩ => ?_⟩
  have hFp := hPF.isPolytope hP
  let b := vertexCentroid F
  have hbF : b ∈ F := vertexCentroid_mem hFp hne
  have hb_zero : ∀ ℓ ∈ L, ℓ b = 0 → ℓ z = 0 := fun ℓ hℓL hb0 => by
    apply hzL₀ ℓ ⟨hℓL, fun y hyF => ?_⟩
    by_contra hne0
    have hlt := hFp.apply_vertexCentroid_lt hne (fun w hw => (hPL ▸ hPF.subset hw) ℓ hℓL)
      hyF (((hPL ▸ hPF.subset hyF) ℓ hℓL).lt_of_ne hne0)
    linarith
  obtain ⟨ε, hε_pos, hmem⟩ := exists_lineMap_mem_setOf_le hL
    (fun ℓ hℓ => (hPL ▸ hPF.subset hbF) ℓ hℓ) hb_zero
  have hwP : AffineMap.lineMap b z (-ε) ∈ P := by
    rw [hPL]; exact hmem (-ε) (by rw [abs_neg, abs_of_pos hε_pos])
  have hopen : b ∈ openSegment ℝ (AffineMap.lineMap b z (-ε)) z := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    simp only [AffineMap.lineMap_apply_module, smul_add, smul_smul, add_assoc, ← add_smul]
    rw [show 1 / (1 + ε) * (1 - -ε) = 1 by field_simp; ring,
      show 1 / (1 + ε) * -ε + ε / (1 + ε) = 0 by field_simp; ring,
      one_smul, zero_smul, add_zero]
  exact hPF.isExtreme.right_mem_of_mem_openSegment hwP hzP hbF hopen

theorem IsPolytopeFace.isExposed {P F : Set E} (hP : IsPolytope P) (hPF : IsPolytopeFace P F) :
    IsExposed ℝ P F := by
  intro hne
  obtain ⟨_, L, hL, hPL⟩ := isPolytope_iff_isHPolytope.1 hP
  obtain ⟨L₀, hL₀, hFeq⟩ := hPF.exists_eq_zero_of_isHPolytope hL hPL hP hne
  rw [hFeq] at hne ⊢
  exact isExposed_of_eq_zero hL hPL hL₀ hne

theorem exists_isPolytopeFace_inter_setOf_le_eq_zero {P R F : Set E} (hP : IsPolytope P)
    {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite) (hR : R = {x | ∀ m ∈ LR, m x ≤ 0})
    (hF : IsPolytopeFace (P ∩ R) F) (hne : F.Nonempty) :
    ∃ P' L₀, IsPolytopeFace P P' ∧ L₀ ⊆ LR ∧ F = P' ∩ {x ∈ R | ∀ m ∈ L₀, m x = 0} := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  have hPR_eq : P ∩ R = {x | ∀ ℓ ∈ LP ∪ LR, ℓ x ≤ 0} := by
    rw [hPeq, hR, setOf_forall_le_inter]
  have hPR : IsPolytope (P ∩ R) :=
    IsHPolytope.isVPolytope ⟨hP.isBounded.subset inter_subset_left, LP ∪ LR, hLP.union hLR, hPR_eq⟩
  obtain ⟨K₀, hK₀, hFeq⟩ := hF.exists_eq_zero_of_isHPolytope (hLP.union hLR) hPR_eq hPR hne
  refine ⟨{x ∈ P | ∀ ℓ ∈ K₀ ∩ LP, ℓ x = 0}, K₀ ∩ LR,
    isPolytopeFace_of_eq_zero hLP hPeq hP.convex inter_subset_right, inter_subset_right, ?_⟩
  rw [hFeq]; ext x; simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨⟨hxP, hxR⟩, hxK⟩ =>
      ⟨⟨hxP, fun ℓ hℓ => hxK ℓ hℓ.1⟩, ⟨hxR, fun ℓ hℓ => hxK ℓ hℓ.1⟩⟩,
    fun ⟨⟨hxP, hxKP⟩, ⟨hxR, hxKR⟩⟩ => ⟨⟨hxP, hxR⟩, fun ℓ hℓ =>
      (hK₀ hℓ).elim (fun h => hxKP ℓ ⟨hℓ, h⟩) fun h => hxKR ℓ ⟨hℓ, h⟩⟩⟩

theorem exists_isPolytopeFace_inter_setOf_le {P R F : Set E} (hP : IsPolytope P)
    {LR : Set (E →ᵃ[ℝ] ℝ)} (hLR : LR.Finite) (hR : R = {x | ∀ m ∈ LR, m x ≤ 0})
    (hF : IsPolytopeFace (P ∩ R) F) (hne : F.Nonempty) :
    ∃ P' R', IsPolytopeFace P P' ∧ IsPolytopeFace R R' ∧ F = P' ∩ R' := by
  have hRc : Convex ℝ R := hR ▸ convex_setOf_forall_le LR
  obtain ⟨P', L₀, hPP', hL₀, hFeq⟩ :=
    exists_isPolytopeFace_inter_setOf_le_eq_zero hP hLR hR hF hne
  exact ⟨P', {x ∈ R | ∀ m ∈ L₀, m x = 0}, hPP',
    isPolytopeFace_of_eq_zero hLR hR hRc hL₀, hFeq⟩

theorem exists_isPolytopeFace_inter_eq {P Q F : Set E} (hP : IsPolytope P) (hQ : IsPolytope Q)
    (hF : IsPolytopeFace (P ∩ Q) F) (hne : F.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ F = P' ∩ Q' := by
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  exact exists_isPolytopeFace_inter_setOf_le hP hLQ hQeq hF hne

theorem exists_isPolytopeFace_preimage_inter_eq {P : Set E} {Q : Set F} (f : E →ᵃ[ℝ] F)
    (hP : IsPolytope P) (hQ : IsPolytope Q) {G : Set E}
    (hG : IsPolytopeFace (P ∩ f ⁻¹' Q) G) (hne : G.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ G = P' ∩ f ⁻¹' Q' := by
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  obtain ⟨P', L₀, hPP', hL₀, hGeq⟩ := exists_isPolytopeFace_inter_setOf_le_eq_zero hP
    (hLQ.image _) (by rw [hQeq, preimage_setOf_forall_le]) hG hne
  refine ⟨P', {y ∈ Q | ∀ m ∈ {m ∈ LQ | m.comp f ∈ L₀}, m y = 0}, hPP',
    isPolytopeFace_of_eq_zero hLQ hQeq hQ.convex (fun _ h => h.1), hGeq.trans ?_⟩
  ext x
  simp only [mem_inter_iff, Set.mem_preimage, mem_ofPred_eq]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun m hm => h3 _ hm.2⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, fun ℓ hℓ => by
      obtain ⟨m, hmQ, rfl⟩ := hL₀ hℓ
      exact h3 m ⟨hmQ, hℓ⟩⟩⟩

omit [FiniteDimensional ℝ E] in
private lemma ray_not_bounded {P : Set E} (hbnd : Bornology.IsBounded P) {b x : E} (hne : x ≠ b)
    (hray : ∀ t : ℝ, 1 ≤ t → AffineMap.lineMap b x t ∈ P) : False := by
  obtain ⟨C, hC⟩ := hbnd.subset_closedBall b
  have hxd : 0 < ‖x - b‖ := norm_sub_pos_iff.2 hne
  set t : ℝ := max 1 ((C + 1) / ‖x - b‖)
  have ht1 : 1 ≤ t := le_max_left _ _
  have hmem := hC (hray t ht1)
  rw [mem_closedBall_iff_norm, AffineMap.lineMap_apply_module] at hmem
  have hnorm : (1 - t) • b + t • x - b = t • (x - b) := by module
  rw [hnorm, norm_smul, Real.norm_of_nonneg (by linarith)] at hmem
  have hC1 : C + 1 ≤ t * ‖x - b‖ := (div_le_iff₀ hxd).1 (le_max_right 1 _)
  linarith

/-- Every point `x ∈ P` other than `vertexCentroid P` lies on a closed segment from
`vertexCentroid P` to a point `y` in some proper nonempty face of `P`. -/
theorem exists_isPolytopeFace_ssubset_of_ne_vertexCentroid {P : Set E} (hP : IsPolytope P)
    {x : E} (hx : x ∈ P) (hxne : x ≠ vertexCentroid P) :
    ∃ F, IsPolytopeFace P F ∧ F.Nonempty ∧ F ⊂ P ∧
      ∃ y ∈ F, x ∈ segment ℝ (vertexCentroid P) y := by
  classical
  obtain ⟨hbnd, L, hL, hPL⟩ := isPolytope_iff_isHPolytope.1 hP
  let b := vertexCentroid P
  have hbP : b ∈ P := vertexCentroid_mem hP ⟨x, hx⟩
  set Linc : Finset (E →ᵃ[ℝ] ℝ) := hL.toFinset.filter (fun ℓ => ℓ b < 0 ∧ ℓ b < ℓ x)
  have hline : ∀ {t : ℝ}, 0 ≤ t →
      (∀ ℓ ∈ Linc, t * (ℓ x - ℓ b) ≤ -ℓ b) → AffineMap.lineMap b x t ∈ P := fun {t} ht hb => by
    rw [hPL]; intro ℓ hℓ; rw [affineMap_lineMap]
    rcases ((hPL ▸ hbP) ℓ hℓ).lt_or_eq with hb_lt | hb0
    · by_cases hinc : ℓ b < ℓ x
      · linarith [hb ℓ (Finset.mem_filter.2 ⟨hL.mem_toFinset.2 hℓ, hb_lt, hinc⟩)]
      · linarith [mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.2 (not_lt.1 hinc))]
    · have h0x : ℓ x = 0 := by_contra fun hne0 => by
        linarith [hP.apply_vertexCentroid_lt ⟨x, hx⟩ (fun w hw => (hPL ▸ hw) ℓ hℓ) hx
          (((hPL ▸ hx) ℓ hℓ).lt_of_ne hne0)]
      rw [hb0, h0x, sub_zero, mul_zero, add_zero]
  have hLinc_ne : Linc.Nonempty := Finset.nonempty_iff_ne_empty.2 fun hmt =>
    ray_not_bounded hbnd hxne fun t ht => hline (by linarith) (by simp [hmt])
  obtain ⟨ℓ₀, hℓ₀, hmin⟩ := Linc.exists_min_image (fun ℓ => (-ℓ b) / (ℓ x - ℓ b)) hLinc_ne
  obtain ⟨hℓ₀L, hℓ₀_lt, hℓ₀_inc⟩ := by
    simpa [Linc, hL.mem_toFinset] using hℓ₀
  have hdiff : 0 < ℓ₀ x - ℓ₀ b := sub_pos.2 hℓ₀_inc
  set t := (-ℓ₀ b) / (ℓ₀ x - ℓ₀ b)
  have ht1 : 1 ≤ t := (one_le_div hdiff).2 (by linarith [(hPL ▸ hx) ℓ₀ hℓ₀L])
  have hyP : AffineMap.lineMap b x t ∈ P := hline (by linarith) fun _ hm =>
    (le_div_iff₀ (sub_pos.2 (Finset.mem_filter.1 hm).2.2)).1 (hmin _ hm)
  have hy0 : ℓ₀ (AffineMap.lineMap b x t) = 0 := by
    rw [affineMap_lineMap, div_mul_cancel₀ _ hdiff.ne']; ring
  refine ⟨{z ∈ P | ℓ₀ z = 0},
    by simpa using isPolytopeFace_of_eq_zero hL hPL hP.convex (singleton_subset_iff.2 hℓ₀L),
    ⟨_, hyP, hy0⟩, ⟨fun _ h => h.1, fun hsub => hℓ₀_lt.ne (hsub hbP).2⟩, _, ⟨hyP, hy0⟩,
    1 - 1 / t, 1 / t, sub_nonneg.2 (div_le_one_of_le₀ ht1 (by linarith)), by positivity,
    by ring, ?_⟩
  rw [AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul,
    show (1 - 1 / t) + 1 / t * (1 - t) = 0 by field_simp; ring,
    show 1 / t * t = 1 by field_simp, zero_smul, one_smul, zero_add]

omit [FiniteDimensional ℝ E] in
private lemma isExtreme_convexHull_of_affineIndependent {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s) :
    IsExtreme ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) := by
  classical
  refine ⟨convexHull_mono (Finset.coe_subset.2 hts), fun x hx y hy z hz hzx => ?_⟩
  obtain ⟨wx, hwx0, hwx1, rfl⟩ := Finset.mem_convexHull'.1 hx
  obtain ⟨wy, hwy0, hwy1, rfl⟩ := Finset.mem_convexHull'.1 hy
  obtain ⟨wz, hwz0, hwz1, hwzeq⟩ := Finset.mem_convexHull'.1 hz
  rcases hzx with ⟨a, b, ha, hb, hab, hzeq⟩
  let c : s → ℝ := fun v => a * wx v.1 + b * wy v.1
  let d : s → ℝ := fun v => if v.1 ∈ t then wz v.1 else 0
  have hc_sum : ∑ v : s, c v = 1 := by
    simp only [c, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_coe_sort, hwx1, hwy1]
    linarith
  have hd_sum : ∑ v : s, d v = 1 := by
    rw [Finset.sum_coe_sort s (fun v => if v ∈ t then wz v else 0),
      ← Finset.sum_subset hts fun _ _ h => ite_eq_right h]
    exact (Finset.sum_congr rfl fun _ h => ite_eq_left h).trans hwz1
  have hcomb : Finset.univ.affineCombination ℝ ((↑) : s → E) c =
      Finset.univ.affineCombination ℝ ((↑) : s → E) d := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hc_sum,
      Finset.affineCombination_eq_linear_combination _ _ _ hd_sum,
      Finset.sum_coe_sort s (fun v => (a * wx v + b * wy v) • v),
      Finset.sum_coe_sort s (fun v => (if v ∈ t then wz v else 0) • v)]
    refine (Finset.sum_congr rfl fun _ _ => by rw [add_smul, ← smul_smul, ← smul_smul]).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hzeq, ← hwzeq,
      ← Finset.sum_subset hts fun _ _ h => by simp [h]]
    exact Finset.sum_congr rfl fun _ h => by simp [h]
  have hcd := hs.injOn_affineCombination_fintypeAffineCoords
    (mem_fintypeAffineCoords_iff_sum.2 hc_sum) (mem_fintypeAffineCoords_iff_sum.2 hd_sum) hcomb
  have hx_supp : ∀ v ∈ s, v ∉ t → wx v = 0 := fun v hvs hvt => by
    have hcv : a * wx v + b * wy v = 0 := by
      simpa only [c, d, hvt, ↓reduceIte] using congrFun hcd ⟨v, hvs⟩
    exact (mul_eq_zero.1 (by nlinarith [hwx0 v hvs, hwy0 v hvs])).resolve_left ha.ne'
  exact Finset.mem_convexHull'.2 ⟨wx, fun v hv => hwx0 v (hts hv),
    (Finset.sum_subset hts hx_supp).trans hwx1,
    Finset.sum_subset hts fun v hvs hvt => by simp [hx_supp v hvs hvt]⟩

theorem IsPolytopeFace.simplex_convexHull_iff {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) {F : Set E} :
    IsPolytopeFace (convexHull ℝ (s : Set E)) F ↔ ∃ t ⊆ s, F = convexHull ℝ (t : Set E) := by
  classical
  refine ⟨fun hPF => ?_, fun ⟨t, hts, ht⟩ =>
    ht ▸ ⟨isExtreme_convexHull_of_affineIndependent hs hts, convex_convexHull ℝ _⟩⟩
  refine ⟨s.filter (· ∈ F), Finset.filter_subset _ _, Subset.antisymm (fun x hx => ?_)
    (convexHull_min (fun _ hv => (Finset.mem_filter.1 hv).2) hPF.convex)⟩
  have hFeq := hPF.eq_convexHull_extremePoints_inter (isPolytope_convexHull s.finite_toSet)
  refine convexHull_mono (fun _ hv => ?_) (hFeq ▸ hx)
  exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨extremePoints_convexHull_subset hv.1, hv.2⟩)

theorem exists_isPolytopeFace_prod_eq {P : Set E} {Q : Set F} (hP : IsPolytope P)
    (hQ : IsPolytope Q) {G : Set (E × F)} (hG : IsPolytopeFace (P ×ˢ Q) G) (hne : G.Nonempty) :
    ∃ P' Q', IsPolytopeFace P P' ∧ IsPolytopeFace Q Q' ∧ G = P' ×ˢ Q' := by
  obtain ⟨_, LP, hLP, hPeq⟩ := isPolytope_iff_isHPolytope.1 hP
  obtain ⟨_, LQ, hLQ, hQeq⟩ := isPolytope_iff_isHPolytope.1 hQ
  obtain ⟨K₀, hK₀, hGeq⟩ := hG.exists_eq_zero_of_isHPolytope
    ((hLP.image _).union (hLQ.image _)) (by rw [hPeq, hQeq, prod_setOf_forall_le]) (hP.prod hQ) hne
  refine ⟨{x ∈ P | ∀ a ∈ {a ∈ LP | a.comp AffineMap.fst ∈ K₀}, a x = 0},
    {y ∈ Q | ∀ b ∈ {b ∈ LQ | b.comp AffineMap.snd ∈ K₀}, b y = 0},
    isPolytopeFace_of_eq_zero hLP hPeq hP.convex (fun _ ha => ha.1),
    isPolytopeFace_of_eq_zero hLQ hQeq hQ.convex (fun _ hb => hb.1), ?_⟩
  rw [hGeq]; ext ⟨x, y⟩; simp only [mem_prod, mem_ofPred_eq]
  exact ⟨fun ⟨⟨hxP, hyQ⟩, hxy⟩ => ⟨⟨hxP, fun _ h => hxy _ h.2⟩, ⟨hyQ, fun _ h => hxy _ h.2⟩⟩,
    fun ⟨⟨hxP, hx'⟩, ⟨hyQ, hy'⟩⟩ => ⟨⟨hxP, hyQ⟩, fun _ hℓ => by
      rcases hK₀ hℓ with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact hx' a ⟨ha, hℓ⟩
      · exact hy' b ⟨hb, hℓ⟩⟩⟩

end FiniteDim

end Cslib.Polyhedra
