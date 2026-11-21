/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Translation
public import Mathlib.Topology.Homeomorph.Lemmas
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters
import CslibFrontier.Foundations.Data.Fin.Order
import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import CslibFrontier.Foundations.Geometry.Polygonal.SegmentCuts
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite polygonal images under a plateau shear

The concrete homeomorphism is constructed by conjugating the existing product shear.
Actual indexed segments are split at four horizontal levels, retaining occurrences and
both loop ends. The finite image has between one and five pieces per original segment.
Its support is the full homeomorphic image; a strictly ordered scalar auxiliary route
transports simplicity without assuming any geometric coordinate monotonicity.

## Interface

* `plateauShear`, `plateauShear_apply`: the actual map and its coordinate formula.
* `Route.plateauShear`: the finite route construction, with literal outer conditionals.
* `Route.eval_plateauShear`: closed-parameter transport, retaining both endpoint tags.
* `Route.support_plateauShear`, `Route.IsSimple.plateauShear`: continuum image and simplicity.
* `Route.germ_plateauShear`: positive end factors at strictly flat endpoint heights.

Global nonlinear evaluation identities are
confined to the unit interval; affine strip branches alone have all-real identities.

This is original finite geometry towards [#3091](https://github.com/cslib-community/cslib-frontier/issues/3091),
not an ambient forest-extension, parity move, HT or recognition theorem.
-/

public section

namespace Cslib.Polygonal


private noncomputable def profile (h r y : ℝ) : ℝ :=
  max 0 (min 1 (2 - 2 * |y - h| / r))

private theorem profile_continuous (h r : ℝ) : Continuous (profile h r) := by
  unfold profile
  fun_prop

private theorem profile_inner {h r y : ℝ} (hr : 0 < r) (hy : |y - h| ≤ r / 2) :
    profile h r y = 1 := by
  have hq : 2 * |y - h| / r ≤ 1 := by
    rw [div_le_iff₀ hr]
    linarith
  simp only [profile, min_eq_left (by linarith : 1 ≤ 2 - 2 * |y - h| / r),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

private theorem profile_outer {h r y : ℝ} (hr : 0 < r) (hy : r ≤ |y - h|) :
    profile h r y = 0 := by
  have hq : 2 ≤ 2 * |y - h| / r := by
    rw [le_div_iff₀ hr]
    linarith
  have hnonpos : 2 - 2 * |y - h| / r ≤ 0 := by linarith
  rw [profile, min_eq_right (hnonpos.trans (by norm_num)), max_eq_left hnonpos]

private theorem profile_nonpos {h r y : ℝ} (hr : r ≤ 0) : profile h r y = 1 := by
  have hq : 2 * |y - h| / r ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hr
  rw [profile, min_eq_left (by linarith), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

private noncomputable def heightCoordinates : ℂ ≃ₜ ℝ × ℝ :=
  Complex.equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ)

private noncomputable def coordinateShear (h r d : ℝ) : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  { Equiv.prodShear (Equiv.refl ℝ) (fun y => Equiv.addLeft (d * profile h r y)) with
    continuous_toFun := by
      change Continuous (fun z : ℝ × ℝ => (z.1, d * profile h r z.1 + z.2))
      exact continuous_fst.prodMk
        ((continuous_const.mul ((profile_continuous h r).comp continuous_fst)).add continuous_snd)
    continuous_invFun := by
      change Continuous (fun z : ℝ × ℝ => (z.1, -(d * profile h r z.1) + z.2))
      exact continuous_fst.prodMk
        ((continuous_const.mul ((profile_continuous h r).comp continuous_fst)).neg.add
          continuous_snd) }

/-- The actual horizontal plateau shear. It has an explicit inverse for arbitrary displacement.
For nonpositive width the same formula is the global translation by `d`; geometric band
properties below require positive width. The first coordinate of the internal product is height. -/
noncomputable def plateauShear (h r d : ℝ) : ℂ ≃ₜ ℂ :=
  heightCoordinates.trans ((coordinateShear h r d).trans heightCoordinates.symm)

/-- The concrete shear preserves height and adds the plateau displacement to the real coordinate. -/
theorem plateauShear_apply (h r d : ℝ) (z : ℂ) :
    plateauShear h r d z = z + (d * max 0 (min 1 (2 - 2 * |z.im - h| / r)) : ℝ) := by
  change Complex.equivRealProdCLM.symm (d * profile h r z.im + z.re, z.im) = _
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, profile]; ring

/-- In the plateau the map is a literal translation, including at its two boundary heights. -/
theorem plateauShear_apply_inner {h r : ℝ} (hr : 0 < r) (d : ℝ) {z : ℂ}
    (hz : |z.im - h| ≤ r / 2) : plateauShear h r d z = z + (d : ℂ) := by
  rw [plateauShear_apply]
  change z + (d * profile h r z.im : ℝ) = _
  rw [profile_inner hr hz, mul_one]

/-- Outside the band every point is fixed, including either outer boundary. -/
theorem plateauShear_apply_outer {h r : ℝ} (hr : 0 < r) (d : ℝ) {z : ℂ}
    (hz : r ≤ |z.im - h|) : plateauShear h r d z = z := by
  rw [plateauShear_apply]
  change z + (d * profile h r z.im : ℝ) = _
  rw [profile_outer hr hz, mul_zero, Complex.ofReal_zero, add_zero]

private noncomputable def levels (h r : ℝ) : Finset ℝ :=
  {h - r, h - r / 2, h + r / 2, h + r}

private noncomputable abbrev strictCuts (h r : ℝ) (a b : ℂ) : Finset ℝ :=
  segmentInteriorCuts (levels h r) a.im b.im

private noncomputable abbrev cuts (h r : ℝ) (a b : ℂ) : List ℝ :=
  segmentCuts (levels h r) a.im b.im

private theorem cuts_length_bounds (h r : ℝ) (a b : ℂ) :
    2 ≤ (cuts h r a b).length ∧ (cuts h r a b).length ≤ 6 := by
  have hc : (strictCuts h r a b).card ≤ 4 := by
    unfold strictCuts segmentInteriorCuts
    split_ifs
    · simp
    · exact (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans
        (by
          change ({h-r,h-r/2,h+r/2,h+r} : Finset ℝ).card ≤ 4
          exact Finset.card_le_four))
  rw [show (cuts h r a b).length = (strictCuts h r a b).card + 2 from
    segmentCuts_length_eq (levels h r) a.im b.im]
  omega

private theorem profile_lower {h r y : ℝ} (hr : 0 < r)
    (hy : y ∈ Set.Icc (h - r) (h - r / 2)) :
    profile h r y = 2 + 2 * (y - h) / r := by
  have habs : |y - h| = -(y - h) := abs_of_nonpos (by linarith [hy.2])
  have hlow : 0 ≤ 2 - 2 * |y - h| / r := by
    rw [habs]
    have hq : 2 * -(y - h) / r ≤ 2 := by
      rw [div_le_iff₀ hr]
      linarith [hy.1]
    linarith
  have hupp : 2 - 2 * |y - h| / r ≤ 1 := by
    rw [habs]
    have hq : 1 ≤ 2 * -(y - h) / r := by
      rw [le_div_iff₀ hr]
      linarith [hy.2]
    linarith
  rw [profile, min_eq_right hupp, max_eq_right hlow, habs]
  ring

private theorem profile_upper {h r y : ℝ} (hr : 0 < r)
    (hy : y ∈ Set.Icc (h + r / 2) (h + r)) :
    profile h r y = 2 - 2 * (y - h) / r := by
  have habs : |y - h| = y - h := abs_of_nonneg (by linarith [hy.1])
  have hlow : 0 ≤ 2 - 2 * |y - h| / r := by
    rw [habs]
    have hq : 2 * (y - h) / r ≤ 2 := by
      rw [div_le_iff₀ hr]
      linarith [hy.2]
    linarith
  have hupp : 2 - 2 * |y - h| / r ≤ 1 := by
    rw [habs]
    have hq : 1 ≤ 2 * (y - h) / r := by
      rw [le_div_iff₀ hr]
      linarith [hy.1]
    linarith
  rw [profile, min_eq_right hupp, max_eq_right hlow, habs]

-- Each branch is an actual affine map. Its line-map identity therefore holds for all
-- real parameters, whereas agreement with the nonlinear shear requires strip membership.
private noncomputable def stripMap (m b : ℝ) : ℂ →ᵃ[ℝ] ℂ :=
  AffineMap.id ℝ ℂ + Complex.ofRealCLM.toLinearMap.toAffineMap.comp
    (m • Complex.imCLM.toLinearMap.toAffineMap + AffineMap.const ℝ ℂ b)

private theorem stripMap_apply (m b : ℝ) (z : ℂ) :
    stripMap m b z = z + (m * z.im + b : ℝ) := by
  simp [stripMap, smul_eq_mul]

private theorem shear_lower {h r : ℝ} (hr : 0 < r) (d : ℝ) {z : ℂ}
    (hz : z.im ∈ Set.Icc (h - r) (h - r / 2)) :
    plateauShear h r d z = stripMap (2 * d / r) (2 * d - 2 * d * h / r) z := by
  rw [plateauShear_apply, stripMap_apply]
  change z + (d * profile h r z.im : ℝ) = _
  rw [profile_lower hr hz]
  congr 2
  ring

private theorem shear_upper {h r : ℝ} (hr : 0 < r) (d : ℝ) {z : ℂ}
    (hz : z.im ∈ Set.Icc (h + r / 2) (h + r)) :
    plateauShear h r d z = stripMap (-2 * d / r) (2 * d + 2 * d * h / r) z := by
  rw [plateauShear_apply, stripMap_apply]
  change z + (d * profile h r z.im : ℝ) = _
  rw [profile_upper hr hz]
  congr 2
  ring

private theorem strip_alternatives {h r lo hi : ℝ}
    (hlevels : ∀ y ∈ levels h r, ¬(lo < y ∧ y < hi)) :
    hi ≤ h - r ∨
      (h - r ≤ lo ∧ hi ≤ h - r / 2) ∨
      (h - r / 2 ≤ lo ∧ hi ≤ h + r / 2) ∨
      (h + r / 2 ≤ lo ∧ hi ≤ h + r) ∨ h + r ≤ lo := by
  by_cases h₀ : hi ≤ h - r
  · exact Or.inl h₀
  have hl₀ : h - r ≤ lo := by
    have hn := hlevels (h - r) (by simp [levels])
    exact le_of_not_gt (fun hh => hn ⟨hh, lt_of_not_ge h₀⟩)
  right
  by_cases h₁ : hi ≤ h - r / 2
  · exact Or.inl ⟨hl₀, h₁⟩
  have hl₁ : h - r / 2 ≤ lo := by
    have hn := hlevels (h - r / 2) (by simp [levels])
    exact le_of_not_gt (fun hh => hn ⟨hh, lt_of_not_ge h₁⟩)
  right
  by_cases h₂ : hi ≤ h + r / 2
  · exact Or.inl ⟨hl₁, h₂⟩
  have hl₂ : h + r / 2 ≤ lo := by
    have hn := hlevels (h + r / 2) (by simp [levels])
    exact le_of_not_gt (fun hh => hn ⟨hh, lt_of_not_ge h₂⟩)
  right
  by_cases h₃ : hi ≤ h + r
  · exact Or.inl ⟨hl₂, h₃⟩
  have hn := hlevels (h + r) (by simp [levels])
  exact Or.inr (le_of_not_gt (fun hh => hn ⟨hh, lt_of_not_ge h₃⟩))

private theorem affine_strip {h r lo hi : ℝ} (hr : 0 < r) (d : ℝ)
    (hn : ∀ y ∈ levels h r, ¬(lo < y ∧ y < hi)) :
    ∃ F : ℂ →ᵃ[ℝ] ℂ, ∀ z : ℂ, z.im ∈ Set.Icc lo hi → plateauShear h r d z = F z := by
  rcases strip_alternatives hn with h₀ | ⟨h₀, h₁⟩ | ⟨h₁, h₂⟩ | ⟨h₂, h₃⟩ | h₃
  · refine ⟨AffineMap.id ℝ ℂ, fun z hz => ?_⟩
    exact plateauShear_apply_outer hr d (by
      rw [abs_of_nonpos (by linarith [hz.2])]
      linarith [hz.2])
  · exact ⟨stripMap (2 * d / r) (2 * d - 2 * d * h / r), fun z hz =>
      shear_lower hr d ⟨h₀.trans hz.1, hz.2.trans h₁⟩⟩
  · refine ⟨stripMap 0 d, fun z hz => ?_⟩
    rw [stripMap_apply, zero_mul, zero_add]
    apply plateauShear_apply_inner hr d
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  · exact ⟨stripMap (-2 * d / r) (2 * d + 2 * d * h / r), fun z hz =>
      shear_upper hr d ⟨h₂.trans hz.1, hz.2.trans h₃⟩⟩
  · refine ⟨AffineMap.id ℝ ℂ, fun z hz => ?_⟩
    exact plateauShear_apply_outer hr d (by
      rw [abs_of_nonneg (by linarith [hz.1])]
      linarith [hz.1])

private theorem shear_lineMap {h r : ℝ} (hr : 0 < r) (d : ℝ) {a b : ℂ}
    (hn : ∀ y ∈ levels h r, ¬(min a.im b.im < y ∧ y < max a.im b.im))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    plateauShear h r d (AffineMap.lineMap a b t) =
      AffineMap.lineMap (plateauShear h r d a) (plateauShear h r d b) t := by
  obtain ⟨F, hF⟩ := affine_strip hr d hn
  have ha : a.im ∈ Set.Icc (min a.im b.im) (max a.im b.im) :=
    ⟨min_le_left _ _, le_max_left _ _⟩
  have hb : b.im ∈ Set.Icc (min a.im b.im) (max a.im b.im) :=
    ⟨min_le_right _ _, le_max_right _ _⟩
  have him : (AffineMap.lineMap a b t).im = AffineMap.lineMap a.im b.im t :=
    Complex.imCLM.toLinearMap.toAffineMap.apply_lineMap a b t
  have hz : (AffineMap.lineMap a b t).im ∈ Set.Icc (min a.im b.im) (max a.im b.im) := by
    rw [him, ← segment_eq_Icc']
    exact lineMap_mem_segment ℝ _ _ ht
  rw [hF _ hz, hF a ha, hF b hb, F.apply_lineMap]

private theorem cut_eval {h r : ℝ} (hr : 0 < r) (d : ℝ) {a b : ℂ} {k : ℕ}
    (hk : k + 1 < (cuts h r a b).length) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    plateauShear h r d (AffineMap.lineMap a b
      (AffineMap.lineMap (cuts h r a b)[k] (cuts h r a b)[k + 1] t)) =
      AffineMap.lineMap
        (plateauShear h r d (AffineMap.lineMap a b (cuts h r a b)[k]))
        (plateauShear h r d (AffineMap.lineMap a b (cuts h r a b)[k + 1])) t := by
  exact segmentCuts_map_lineMap (levels h r) Complex.imCLM.toLinearMap.toAffineMap
    (plateauShear h r d) (fun a b hn t ht => shear_lineMap hr d hn ht) a b hk ht

private noncomputable def sourceBlock (p : Route) (h r : ℝ) (i : Fin p.segments) :
    List (Fin p.segments × ℝ) :=
  (cuts h r (p.point i.castSucc) (p.point i.succ)).dropLast.map fun t => (i, t)

private noncomputable def sourceSamples (p : Route) (h r : ℝ) : List (Fin p.segments × ℝ) :=
  ((List.finRange p.segments).flatMap (sourceBlock p h r)) ++
      [(Fin.last p.bends, 1)]

private def sourcePosition {p : Route} (x : Fin p.segments × ℝ) : ℝ :=
  (x.1.val : ℝ) + x.2

private theorem sourceSamples_bounds (p : Route) (h r : ℝ)
    {x : Fin p.segments × ℝ} (hx : x ∈ sourceSamples p h r) : x.2 ∈ Set.Icc 0 1 := by
  simp only [sourceSamples] at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp hx
    change x ∈ (cuts h r (p.point i.castSucc) (p.point i.succ)).dropLast.map (fun t => (i,t)) at ht
    obtain ⟨t, hcut, heq⟩ := List.mem_map.mp ht
    subst x
    exact ⟨(segmentCuts_dropLast_bounds hcut).1, (segmentCuts_dropLast_bounds hcut).2.le⟩
  · have he : x = (Fin.last p.bends, 1) := List.mem_singleton.mp hx
    rw [he]
    constructor <;> norm_num

private theorem sourceSamples_ordered (p : Route) (h r : ℝ) :
    (sourceSamples p h r).Pairwise (fun a b => sourcePosition a < sourcePosition b) := by
  rw [sourceSamples, List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_flatMap]
    constructor
    · intro i _
      apply List.pairwise_map.mpr
      have hc := (segmentCuts_sorted (levels h r)
        (p.point i.castSucc).im (p.point i.succ).im).pairwise
      exact (hc.sublist (List.dropLast_sublist _)).imp
        (fun hab => by dsimp [sourcePosition]; linarith)
    · apply (List.sortedLT_finRange p.segments).pairwise.imp
      intro i j hij x hx y hy
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      have hstep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
      have hs' := segmentCuts_dropLast_bounds hs
      have ht' := segmentCuts_dropLast_bounds ht
      dsimp [sourcePosition]
      linarith
  · intro x hx y hy
    obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp hx
    change x ∈ (cuts h r (p.point i.castSucc) (p.point i.succ)).dropLast.map (fun t => (i,t)) at ht
    obtain ⟨t, hcut, rfl⟩ := List.mem_map.mp ht
    have hy' : y = (Fin.last p.bends, 1) := List.mem_singleton.mp hy
    subst y
    have hi : i.val ≤ p.bends := by have := i.isLt; dsimp [Route.segments] at *; omega
    have hi' : (i.val : ℝ) ≤ p.bends := by exact_mod_cast hi
    have ht' := segmentCuts_dropLast_bounds hcut
    dsimp [sourcePosition]
    linarith

private theorem sourceBlock_length (p : Route) (h r : ℝ) (i : Fin p.segments) :
    1 ≤ (sourceBlock p h r i).length ∧ (sourceBlock p h r i).length ≤ 5 := by
  have hc := cuts_length_bounds h r (p.point i.castSucc) (p.point i.succ)
  simp only [sourceBlock, List.length_map, List.length_dropLast]
  omega

private theorem sourceBlock_ne_nil (p : Route) (h r : ℝ) (i : Fin p.segments) :
    sourceBlock p h r i ≠ [] := by
  have := sourceBlock_length p h r i
  intro he
  rw [he] at this
  simp at this

private theorem sourceBlock_head (p : Route) (h r : ℝ) (i : Fin p.segments) :
    (sourceBlock p h r i).head (sourceBlock_ne_nil p h r i) = (i, 0) := by
  rw [List.head_eq_getElem]
  simp only [sourceBlock, List.getElem_map, List.getElem_dropLast,
    (segmentCuts_first_last (levels h r) (p.point i.castSucc).im (p.point i.succ).im).1]

private theorem sourceBlock_last (p : Route) (h r : ℝ) (i : Fin p.segments) :
    (sourceBlock p h r i).getLast (sourceBlock_ne_nil p h r i) =
      (i, (cuts h r (p.point i.castSucc) (p.point i.succ))[
        (cuts h r (p.point i.castSucc) (p.point i.succ)).length - 2]'(by
          have := cuts_length_bounds h r (p.point i.castSucc) (p.point i.succ); omega)) := by
  rw [List.getLast_eq_getElem]
  simp only [sourceBlock, List.length_map, List.length_dropLast, List.getElem_map,
    List.getElem_dropLast, Nat.sub_sub]

private theorem sourceSamples_length_eq_sum (p : Route) (h r : ℝ) :
    (sourceSamples p h r).length =
      (∑ i : Fin p.segments, (sourceBlock p h r i).length) + 1 := by
  simp only [sourceSamples, List.length_append, List.length_singleton, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

private theorem sourceSamples_length (p : Route) (h r : ℝ) :
    p.segments + 1 ≤ (sourceSamples p h r).length ∧
      (sourceSamples p h r).length ≤ 5 * p.segments + 1 := by
  have hlo : p.segments ≤ ∑ i : Fin p.segments, (sourceBlock p h r i).length := by
    calc
      _ = ∑ _i : Fin p.segments, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => (sourceBlock_length p h r i).1
  have hhi : (∑ i : Fin p.segments, (sourceBlock p h r i).length) ≤ 5 * p.segments := by
    calc
      _ ≤ ∑ _i : Fin p.segments, (5 : ℕ) :=
        Finset.sum_le_sum fun i _ => (sourceBlock_length p h r i).2
      _ = _ := by simp [Nat.mul_comm]
  rw [sourceSamples_length_eq_sum]
  omega

private theorem sourceSamples_nontrivial (p : Route) (h r : ℝ) :
    ∃ x y rest, sourceSamples p h r = x :: y :: rest := by
  have hn := sourceSamples_length p h r
  cases hw : sourceSamples p h r with
  | nil => simp only [hw,List.length_nil,Route.segments] at hn; omega
  | cons x xs =>
    cases xs with
    | nil => simp only [hw,List.length_singleton,Route.segments] at hn; omega
    | cons y rest => exact ⟨x,y,rest,rfl⟩

private theorem sourceSamples_ends (p : Route) (h r : ℝ) :
    (sourceSamples p h r)[0]'(by have := sourceSamples_length p h r; omega) = (0, 0) ∧
      (sourceSamples p h r)[(sourceSamples p h r).length - 1]'(by
        have := sourceSamples_length p h r; omega) = (Fin.last p.bends, 1) := by
  have hfin : List.finRange p.segments ≠ [] := by
    intro he
    have hn := congrArg List.length he
    simp only [List.length_finRange, List.length_nil, Route.segments] at hn
    omega
  have hflat : ((List.finRange p.segments).flatMap (sourceBlock p h r)) ≠ [] :=
    List.flatMap_ne_nil hfin (fun i _ => sourceBlock_ne_nil p h r i)
  have hsource : sourceSamples p h r ≠ [] := by
    intro hz
    have hn := sourceSamples_length p h r
    simp only [hz, List.length_nil] at hn
    omega
  constructor
  · rw [← List.head_eq_getElem hsource]
    have hh : (((List.finRange p.segments).flatMap (sourceBlock p h r)) ++
        [(Fin.last p.bends,1)]).head (by simp) = (0,0) := by
      rw [List.head_append_of_ne_nil hflat,
        List.head_flatMap hfin (fun i _ => sourceBlock_ne_nil p h r i), sourceBlock_head]
      congr 1
      apply Fin.ext
      simp [List.head_eq_getElem]
    exact hh
  · rw [← List.getLast_eq_getElem hsource]
    have he : (((List.finRange p.segments).flatMap (sourceBlock p h r)) ++
        [(Fin.last p.bends,1)]).getLast (by simp) = (Fin.last p.bends,1) := by
      rw [List.getLast_append_of_ne_nil (by simp) (List.cons_ne_nil _ _), List.getLast_singleton]
    exact he

-- The two source descriptions at a shared old knot are retained; only their geometric
-- endpoint equality is used. No lookup by geometric point value occurs here.
private theorem final_cut_endpoint (h r : ℝ) (a b : ℂ) :
    (cuts h r a b)[(cuts h r a b).length - 2 + 1]'(by
      have hlen := cuts_length_bounds h r a b
      omega) = 1 := by
  have hlen := cuts_length_bounds h r a b
  have hidx : (cuts h r a b).length - 2 + 1 = (cuts h r a b).length - 1 := by omega
  simpa only [hidx] using (segmentCuts_first_last (levels h r) a.im b.im).2

private theorem sourceSamples_adjacent (p : Route) (h r : ℝ)
    {x y : Fin p.segments × ℝ} (hxy : (x, y) ∈ (sourceSamples p h r).consecutivePairs) :
    ∃ (i : Fin p.segments) (k : ℕ)
      (hk : k + 1 < (cuts h r (p.point i.castSucc) (p.point i.succ)).length),
      p.eval x.1 x.2 = p.eval i (cuts h r (p.point i.castSucc) (p.point i.succ))[k] ∧
      p.eval y.1 y.2 = p.eval i (cuts h r (p.point i.castSucc) (p.point i.succ))[k + 1] ∧
      sourcePosition x = p.position i (cuts h r (p.point i.castSucc) (p.point i.succ))[k] ∧
      sourcePosition y = p.position i (cuts h r (p.point i.castSucc) (p.point i.succ))[k + 1] := by
  let L := List.finRange p.segments
  let f := sourceBlock p h r
  have hL : L ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [L, List.length_finRange, List.length_nil, Route.segments] at this
    omega
  have hf (i : Fin p.segments) : f i ≠ [] := sourceBlock_ne_nil p h r i
  have hflat := List.flatMap_ne_nil hL (fun i _ => hf i)
  rw [sourceSamples, List.consecutivePairs_append hflat (List.cons_ne_nil _ _)] at hxy
  rcases List.mem_append.mp hxy with hxy | hxy
  · rcases (List.mem_consecutivePairs_flatMap hL hf).mp hxy with
      ⟨i, _, hxy⟩ | ⟨⟨i, j⟩, hij, hx, hy⟩
    · obtain ⟨k, hk, hx, hy⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hxy
      have hk' : k + 1 < (cuts h r (p.point i.castSucc) (p.point i.succ)).length := by
        dsimp [f, sourceBlock] at hk
        simp only [List.length_map, List.length_dropLast] at hk
        omega
      have hx' : x = (i, (cuts h r (p.point i.castSucc) (p.point i.succ))[k]) := by
        rw [← hx]
        simp only [f, sourceBlock, List.getElem_map, List.getElem_dropLast]
      have hy' : y = (i, (cuts h r (p.point i.castSucc) (p.point i.succ))[k + 1]) := by
        rw [← hy]
        simp only [f, sourceBlock, List.getElem_map, List.getElem_dropLast]
      rw [hx', hy']
      exact ⟨i, k, hk', rfl, rfl, rfl, rfl⟩
    · obtain ⟨k, hk, hi, hj⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hij
      have hji : j.val = i.val + 1 := by
        have hi' := congrArg Fin.val hi
        have hj' := congrArg Fin.val hj
        simp [L] at hi' hj'
        omega
      have hnodes : j.castSucc = i.succ := Fin.ext hji
      rw [sourceBlock_last] at hx
      rw [sourceBlock_head] at hy
      subst x
      subst y
      let C := cuts h r (p.point i.castSucc) (p.point i.succ)
      have hlen := cuts_length_bounds h r (p.point i.castSucc) (p.point i.succ)
      have hend := final_cut_endpoint h r (p.point i.castSucc) (p.point i.succ)
      refine ⟨i, C.length - 2, by dsimp [C]; omega, rfl, ?_, rfl, ?_⟩
      · rw [hend]
        simp only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
          hnodes]
      · rw [hend]
        dsimp [sourcePosition, Route.position]
        push_cast [hji]
        ring
  · rcases List.mem_cons.mp hxy with heq | hempty
    · have hlast : L.getLast hL = Fin.last p.bends := by
        apply Fin.ext
        simp [List.getLast_eq_getElem, L, Route.segments]
      have hx : x = (f (Fin.last p.bends)).getLast (hf _) := by
        have he := congrArg Prod.fst heq
        simpa only [List.getLast_flatMap hL (fun i _ => hf i), hlast] using he
      have hy : y = (Fin.last p.bends, 1) := by
        have he := congrArg Prod.snd heq
        simpa only [List.head_cons] using he
      rw [sourceBlock_last] at hx
      subst x
      subst y
      let i := Fin.last p.bends
      let C := cuts h r (p.point i.castSucc) (p.point i.succ)
      have hlen := cuts_length_bounds h r (p.point i.castSucc) (p.point i.succ)
      have hend := final_cut_endpoint h r (p.point i.castSucc) (p.point i.succ)
      refine ⟨i, C.length - 2, by dsimp [C]; omega, rfl, ?_, rfl, ?_⟩
      · rw [hend]
      · dsimp only [sourcePosition, Route.position, i, Fin.val_last]
        rw [hend]
    · simp only [List.consecutivePairs_singleton, List.not_mem_nil] at hempty

private noncomputable def rawShear (p : Route) (h r d : ℝ) : Route :=
  match sourceSamples p h r with
  | x :: y :: rest =>
      (rest.map fun z => plateauShear h r d (p.eval z.1 z.2)).foldl Route.append
        (Route.line (plateauShear h r d (p.eval x.1 x.2))
          (plateauShear h r d (p.eval y.1 y.2)))
  | _ => p

private theorem rawShear_segments (p : Route) (h r d : ℝ) :
    (rawShear p h r d).segments = (sourceSamples p h r).length - 1 := by
  obtain ⟨x,y,rest,hw⟩ := sourceSamples_nontrivial p h r
  simp only [rawShear, hw, Route.segments_foldl_append, Route.segments, Route.line,
    List.length_map, List.length_cons]
  omega

private theorem rawShear_nodeCount (p : Route) (h r d : ℝ) :
    (rawShear p h r d).bends + 2 = (sourceSamples p h r).length := by
  have hseg := rawShear_segments p h r d
  have hlen := sourceSamples_length p h r
  dsimp only [Route.segments] at hseg
  omega

-- A scalar auxiliary route, not the geometric image route, records old chain positions.
-- Its strict real order is the existing CoordinateOrder caller that permits arbitrary loops.
private noncomputable def parameterRoute (p : Route) (h r d : ℝ) : Route where
  bends := (rawShear p h r d).bends
  point := fun i => (sourcePosition ((sourceSamples p h r)[i.val]'(by
    rw [← rawShear_nodeCount p h r d]
    exact i.isLt)) : ℝ)

private theorem parameterRoute_ordered (p : Route) (h r d : ℝ) :
    StrictMono fun i => ((parameterRoute p h r d).point i).re := by
  intro i j hij
  have hm := List.pairwise_iff_get.mp (sourceSamples_ordered p h r)
  exact hm _ _ (show (⟨i.val, by rw [← rawShear_nodeCount p h r d]; exact i.isLt⟩ :
    Fin (sourceSamples p h r).length) < ⟨j.val, by
      rw [← rawShear_nodeCount p h r d]; exact j.isLt⟩ from hij)

private theorem parameterRoute_ends (p : Route) (h r d : ℝ) :
    (parameterRoute p h r d).start = 0 ∧
      (parameterRoute p h r d).finish = (p.segments : ℝ) := by
  have he := sourceSamples_ends p h r
  constructor
  · simp only [parameterRoute, Route.start, Fin.val_zero, he.1, sourcePosition,
      Fin.val_zero, Nat.cast_zero, zero_add, Complex.ofReal_zero]
  · have hlast : (rawShear p h r d).segments = (sourceSamples p h r).length - 1 :=
      rawShear_segments p h r d
    simp only [parameterRoute, Route.finish, Fin.val_last, hlast, he.2, sourcePosition,
      Fin.val_last, Route.segments, Nat.cast_add, Nat.cast_one]

private theorem rawShear_adjacent (p : Route) (h r d : ℝ)
    (i : Fin (rawShear p h r d).segments) :
    let W := sourceSamples p h r
    let x := W[i.val]'(by
      have hi := i.isLt
      have hseg := rawShear_segments p h r d
      change _ < (sourceSamples p h r).length
      omega)
    let y := W[i.val + 1]'(by
      have hi := i.isLt
      have hseg := rawShear_segments p h r d
      change _ < (sourceSamples p h r).length
      omega)
    (∀ t : ℝ, (rawShear p h r d).eval i t =
      AffineMap.lineMap (plateauShear h r d (p.eval x.1 x.2))
        (plateauShear h r d (p.eval y.1 y.2)) t) ∧
    (∀ t : ℝ, ((parameterRoute p h r d).eval i t).re =
      AffineMap.lineMap (sourcePosition x) (sourcePosition y) t) := by
  obtain ⟨x,y,rest,hw⟩ := sourceSamples_nontrivial p h r
  have hraw : rawShear p h r d =
      (rest.map fun z => plateauShear h r d (p.eval z.1 z.2)).foldl Route.append
        (Route.line (plateauShear h r d (p.eval x.1 x.2))
          (plateauShear h r d (p.eval y.1 y.2))) := by simp only [rawShear, hw]
  dsimp only
  constructor
  · intro t
    let F : Fin p.segments × ℝ → ℂ := fun z => plateauShear h r d (p.eval z.1 z.2)
    let A : ℂ := F x
    let B : ℂ := F y
    let nodes : List ℂ := rest.map F
    let q : Route := nodes.foldl Route.append (Route.line A B)
    have heq : rawShear p h r d = q := hraw
    have hnode : ∀ (q' : Route), rawShear p h r d = q' →
        ∀ (n : ℕ) (hn : n < (rawShear p h r d).bends+2) (hm : n < q'.bends+2),
        (rawShear p h r d).point ⟨n,hn⟩ = q'.point ⟨n,hm⟩ := by
      intro q' he
      subst q'
      intros
      rfl
    have hi : i.val < q.segments := heq ▸ i.isLt
    have hev : (rawShear p h r d).eval i t = q.eval ⟨i.val,hi⟩ t := by
      unfold Route.eval
      congr 2
      · exact hnode q heq i.val i.castSucc.isLt (Fin.castSucc ⟨i.val,hi⟩).isLt
      · exact hnode q heq (i.val+1) i.succ.isLt (Fin.succ ⟨i.val,hi⟩).isLt
    rw [hev]
    have heall := Route.eval_foldl_append_line A B nodes
    have he := heall ⟨i.val,hi⟩ t
    have hword : A :: B :: nodes = (x :: y :: rest).map F := rfl
    simpa only [hword, hw, List.getElem_map, F] using he
  · intro t
    have hi := i.isLt
    have hseg := rawShear_segments p h r d
    change (AffineMap.lineMap
      ((sourcePosition ((sourceSamples p h r)[i.val])) : ℂ)
      ((sourcePosition ((sourceSamples p h r)[i.val+1])) : ℂ) t).re = _
    simp only [AffineMap.lineMap_apply_module', Complex.add_re, Complex.smul_re,
      Complex.sub_re, Complex.ofReal_re]


private theorem rawShear_parameter {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ)
    (i : Fin (rawShear p h r d).segments) :
    ∃ (j : Fin p.segments) (α β : ℝ),
      0 ≤ α ∧ α < β ∧ β ≤ 1 ∧
      (∀ y ∈ levels h r, ¬(min (p.eval j α).im (p.eval j β).im < y ∧
        y < max (p.eval j α).im (p.eval j β).im)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (rawShear p h r d).eval i t =
          plateauShear h r d (p.eval j (AffineMap.lineMap α β t))) ∧
      (∀ t : ℝ, ((parameterRoute p h r d).eval i t).re =
        p.position j (AffineMap.lineMap α β t)) := by
  have hidx : i.val + 1 < (sourceSamples p h r).length := by
    have := i.isLt
    have hseg := rawShear_segments p h r d
    omega
  obtain ⟨heval, hpos⟩ := rawShear_adjacent p h r d i
  obtain ⟨j, k, hk, hx, hy, hxp, hyp⟩ := sourceSamples_adjacent p h r
    (List.getElem_mem_consecutivePairs (sourceSamples p h r) i.val hidx)
  let C := cuts h r (p.point j.castSucc) (p.point j.succ)
  have hkC : k + 1 < C.length := hk
  have hα := segmentCuts_mem_Icc (List.getElem_mem (by omega : k < C.length))
  have hβ := segmentCuts_mem_Icc (List.getElem_mem hk)
  have hαβ : C[k] < C[k + 1] := (segmentCuts_sorted (levels h r) _ _).strictMono_get
    (show (⟨k, by omega⟩ : Fin C.length) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
  refine ⟨j, C[k], C[k + 1], hα.1, hαβ, hβ.2, ?_, ?_, ?_⟩
  · exact segmentCuts_adjacent_no_level (levels h r) Complex.imCLM.toLinearMap.toAffineMap
      (a := p.point j.castSucc) (b := p.point j.succ) hk
  · intro t ht
    rw [heval, hx, hy]
    exact (cut_eval hr d hk ht).symm
  · intro t
    rw [hpos, hxp, hyp]
    change AffineMap.lineMap ((j.val : ℝ) + C[k]) ((j.val : ℝ) + C[k + 1]) t =
      (j.val : ℝ) + AffineMap.lineMap C[k] C[k + 1] t
    simp only [AffineMap.lineMap_apply_ring']
    ring

private theorem parameterRoute_real (p : Route) (h r d : ℝ)
    (i : Fin (rawShear p h r d).segments) (t : ℝ) :
    (parameterRoute p h r d).eval i t =
      (((parameterRoute p h r d).eval i t).re : ℝ) := by
  apply Complex.ext
  · simp
  · simp [Route.eval, parameterRoute, AffineMap.lineMap_apply_module']

private theorem parameterRoute_open (p : Route) (h r d : ℝ) :
    (parameterRoute p h r d).start ≠ (parameterRoute p h r d).finish := by
  rw [(parameterRoute_ends p h r d).1, (parameterRoute_ends p h r d).2]
  have hn : (0 : ℝ) < p.segments := by exact_mod_cast Nat.zero_lt_succ p.bends
  exact_mod_cast ne_of_lt hn

private theorem rawShear_atEnd (p : Route) (h r d : ℝ)
    (i : Fin (rawShear p h r d).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (b : Bool) :
    (rawShear p h r d).AtEnd i t b ↔
      ((parameterRoute p h r d).eval i t).re = if b then (p.segments : ℝ) else 0 := by
  let q := parameterRoute p h r d
  have hq := Route.isSimple_of_strictMono_re (parameterRoute_ordered p h r d)
  have hend (b : Bool) : q.endpoint b = (if b then (p.segments : ℝ) else 0 : ℝ) := by
    cases b <;> simp only [q, Route.endpoint, Bool.false_eq_true, ↓reduceIte,
      (parameterRoute_ends p h r d).1, (parameterRoute_ends p h r d).2, Complex.ofReal_zero]
  constructor
  · intro he
    have he' : q.AtEnd i t b := he
    rw [q.at_eq_endpoint i ht b he', hend]
    simp
  · intro he
    have hc : q.eval i t = q.endpoint b := by
      rw [parameterRoute_real p h r d i t, he, hend]
    cases b
    · have hz : q.eval 0 0 = q.endpoint false := by simp [Route.eval, Route.endpoint, Route.start]
      have hp := hq.position_eq_of_eval_eq (parameterRoute_open p h r d) i 0 ht
        (by constructor <;> norm_num) (hc.trans hz.symm)
      simpa only [Route.AtEnd, Bool.false_eq_true, ↓reduceIte, Route.position,
        Fin.val_zero, Nat.cast_zero, add_zero] using hp
    · have hz : q.eval (Fin.last q.bends) 1 = q.endpoint true := by
        simp [Route.eval, Route.endpoint, Route.finish, Route.segments]
      have hp := hq.position_eq_of_eval_eq (parameterRoute_open p h r d) i (Fin.last q.bends) ht
        (by constructor <;> norm_num) (hc.trans hz.symm)
      simpa only [q, parameterRoute, Route.AtEnd, ↓reduceIte, Route.position, Fin.val_last,
        Route.segments,
        Nat.cast_add, Nat.cast_one] using hp

private theorem rawShear_simple {h r : ℝ} (hr : 0 < r) {p : Route} (hp : p.IsSimple)
    (d : ℝ) : (rawShear p h r d).IsSimple := by
  intro i j s t hs ht heq
  obtain ⟨k, α, β, hα, hαβ, hβ, _hlevels, hi, hip⟩ := rawShear_parameter hr p d i
  obtain ⟨l, γ, δ, hγ, hγδ, hδ, _hlevels, hj, hjp⟩ := rawShear_parameter hr p d j
  have hs' : AffineMap.lineMap α β s ∈ Set.Icc (0 : ℝ) 1 := by
    have hm := lineMap_mem_segment ℝ α β hs
    rw [segment_eq_Icc hαβ.le] at hm
    exact ⟨hα.trans hm.1, hm.2.trans hβ⟩
  have ht' : AffineMap.lineMap γ δ t ∈ Set.Icc (0 : ℝ) 1 := by
    have hm := lineMap_mem_segment ℝ γ δ ht
    rw [segment_eq_Icc hγδ.le] at hm
    exact ⟨hγ.trans hm.1, hm.2.trans hδ⟩
  have he := (plateauShear h r d).injective ((hi s hs).symm.trans (heq.trans (hj t ht)))
  rcases hp k l _ _ hs' ht' he with he | ⟨he₀, he₁⟩ | ⟨he₁, he₀⟩
  · left
    have hc : (parameterRoute p h r d).eval i s = (parameterRoute p h r d).eval j t := by
      rw [parameterRoute_real p h r d i s, parameterRoute_real p h r d j t, hip, hjp, he]
    exact (Route.isSimple_of_strictMono_re (parameterRoute_ordered p h r d)).position_eq_of_eval_eq
      (parameterRoute_open p h r d) i j hs ht hc
  · right
    left
    exact ⟨(rawShear_atEnd p h r d i hs false).mpr ((hip s).trans he₀),
      (rawShear_atEnd p h r d j ht true).mpr ((hjp t).trans he₁)⟩
  · right
    right
    exact ⟨(rawShear_atEnd p h r d i hs true).mpr ((hip s).trans he₁),
      (rawShear_atEnd p h r d j ht false).mpr ((hjp t).trans he₀)⟩

private theorem rawShear_endpoint {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ) (b : Bool) :
    (rawShear p h r d).endpoint b = plateauShear h r d (p.endpoint b) := by
  let i : Fin (rawShear p h r d).segments := if b then Fin.last (rawShear p h r d).bends else 0
  let t : ℝ := if b then 1 else 0
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by cases b <;> constructor <;> norm_num [t]
  have he : (rawShear p h r d).AtEnd i t b := by
    cases b <;> simp [Route.AtEnd, Route.position, i, t, Route.segments]
  obtain ⟨j, α, β, hα, hαβ, hβ, _hlevels, hj, hjp⟩ := rawShear_parameter hr p d i
  have hu : AffineMap.lineMap α β t ∈ Set.Icc (0 : ℝ) 1 := by
    have hm := lineMap_mem_segment ℝ α β ht
    rw [segment_eq_Icc hαβ.le] at hm
    exact ⟨hα.trans hm.1, hm.2.trans hβ⟩
  have hje : p.AtEnd j (AffineMap.lineMap α β t) b :=
    (hjp t).symm.trans ((rawShear_atEnd p h r d i ht b).mp he)
  rw [← (rawShear p h r d).at_eq_endpoint i ht b he, hj t ht,
    p.at_eq_endpoint j hu b hje]

private theorem sourceSamples_piece (p : Route) (h r : ℝ) (j : Fin p.segments) {k : ℕ}
    (hk : k + 1 < (cuts h r (p.point j.castSucc) (p.point j.succ)).length) :
    ∃ (q : ℕ) (hq : q + 1 < (sourceSamples p h r).length),
      (sourceSamples p h r)[q] = (j, (cuts h r (p.point j.castSucc) (p.point j.succ))[k]) ∧
      p.eval ((sourceSamples p h r)[q + 1]).1 ((sourceSamples p h r)[q + 1]).2 =
        p.eval j (cuts h r (p.point j.castSucc) (p.point j.succ))[k + 1] := by
  let L := List.finRange p.segments
  let f := sourceBlock p h r
  let C := cuts h r (p.point j.castSucc) (p.point j.succ)
  have hdef : sourceSamples p h r = L.flatMap f ++ [(Fin.last p.bends,1)] := rfl
  have hLlen : L.length = p.segments := List.length_finRange
  have hkC : k+1 < C.length := hk
  let prefLen := ((L.take j.val).flatMap f).length
  have hj : j.val < L.length := by simpa only [L, List.length_finRange] using j.isLt
  have hget : L[j.val] = j := by simp [L]
  have hkf : k < (f L[j.val]).length := by
    simp only [hget, f, sourceBlock, List.length_map, List.length_dropLast]
    omega
  have hq0 := List.flatMap_prefix_add_lt L f hj hkf
  have hq : prefLen + k + 1 < (sourceSamples p h r).length := by
    rw [hdef, List.length_append, List.length_singleton]
    change prefLen+k < (L.flatMap f).length at hq0
    omega
  refine ⟨prefLen + k, hq, ?_, ?_⟩
  · have hget0 : (sourceSamples p h r)[prefLen+k] = (L.flatMap f)[prefLen+k] :=
      List.getElem_append_left (bs := [(Fin.last p.bends,1)]) hq0
    rw [hget0,
      List.getElem_flatMap_prefix_add L f hj hkf]
    simp only [hget, f, sourceBlock, List.getElem_map, List.getElem_dropLast]
  · by_cases hnext : k + 1 < (f j).length
    · have hq1 := List.flatMap_prefix_add_lt L f hj (hget.symm ▸ hnext)
      have hget1 : (sourceSamples p h r)[prefLen+k+1] = (L.flatMap f)[prefLen+k+1] :=
        List.getElem_append_left (bs := [(Fin.last p.bends,1)]) hq1
      rw [hget1]
      have hge : (L.flatMap f)[prefLen+k+1] = (f j)[k+1] := by
        simpa only [prefLen, Nat.add_assoc, hget] using
          List.getElem_flatMap_prefix_add L f hj (hget.symm ▸ hnext)
      rw [hge]
      simp only [f, sourceBlock, List.getElem_map, List.getElem_dropLast]
    · have hkLast : k + 1 = (f j).length := by
        simp only [f, sourceBlock, List.length_map, List.length_dropLast] at hnext ⊢
        omega
      have hfinish : C[k + 1] = 1 := by
        have hlen := cuts_length_bounds h r (p.point j.castSucc) (p.point j.succ)
        have hkLast' : k + 1 = C.length - 1 := by simpa only
          [f, sourceBlock, List.length_map, List.length_dropLast] using hkLast
        simp only [hkLast']
        exact (segmentCuts_first_last (levels h r) (p.point j.castSucc).im (p.point j.succ).im).2
      have hpref : ((L.take (j.val + 1)).flatMap f).length = prefLen + (f j).length := by
        rw [List.take_succ_eq_append_getElem hj, List.flatMap_append,
          List.flatMap_singleton, List.length_append, hget]
      by_cases hjnext : j.val + 1 < p.segments
      · let j' : Fin p.segments := ⟨j.val + 1, hjnext⟩
        have hj' : j'.val < L.length := by change j.val+1 < L.length; omega
        have hhead : L[j'.val] = j' := by simp [L, j']
        have hz : 0 < (f L[j'.val]).length := by
          rw [hhead]
          exact (sourceBlock_length p h r j').1
        have hflat := List.flatMap_prefix_add_lt L f hj' hz
        have hq1 : prefLen + k + 1 = ((L.take j'.val).flatMap f).length + 0 := by
          simp only [j', hpref, add_zero]
          omega
        have hqlem : (sourceSamples p h r)[prefLen+k+1] =
            (f j')[0]'(by rw [← hhead]; exact hz) := by
          have helem' : (sourceSamples p h r)[((L.take j'.val).flatMap f).length+0] =
              (L.flatMap f)[((L.take j'.val).flatMap f).length+0] :=
            List.getElem_append_left (bs := [(Fin.last p.bends,1)]) hflat
          have heget := List.getElem_flatMap_prefix_add L f hj' hz
          have hfinal := helem'.trans heget
          simpa only [← hq1, hhead] using hfinal
        rw [hqlem]
        have hzero : (f j')[0]'(by rw [← hhead]; exact hz) = (j', 0) := by
          simpa only [List.head_eq_getElem] using sourceBlock_head p h r j'
        rw [hzero, hfinish]
        simp only [Route.eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
        congr 1
      · have hjlast : j = Fin.last p.bends := by
          apply Fin.ext
          change j.val = p.bends
          have hn := j.isLt
          change j.val < p.bends+1 at hn
          change ¬j.val+1 < p.bends+1 at hjnext
          omega
        have hfull : prefLen + k + 1 = (L.flatMap f).length := by
          have hjlen : j.val + 1 = L.length := by
            rw [hjlast, Fin.val_last, hLlen]
          rw [hjlen, List.take_length] at hpref
          omega
        have hqlem : (sourceSamples p h r)[prefLen+k+1] = (Fin.last p.bends,1) := by
          have helem := List.getElem_append_right (as := L.flatMap f) (bs := [(Fin.last p.bends,1)])
            (h₂ := by simp only [List.length_append, List.length_singleton]; omega)
            (le_refl (L.flatMap f).length)
          have hget : (sourceSamples p h r)[(L.flatMap f).length] = (Fin.last p.bends,1) := by
            simpa only [← hdef, Nat.sub_self, List.getElem_cons_zero] using helem
          simpa only [hfull] using hget
        rw [hqlem]
        change p.eval (Fin.last p.bends) 1 = p.eval j C[k+1]
        rw [hfinish, hjlast]

private theorem rawShear_contains {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ)
    (j : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    plateauShear h r d (p.eval j t) ∈ (rawShear p h r d).support := by
  obtain ⟨k, hk, hlo, hhi⟩ := segmentCuts_cover (levels := levels h r)
    (a := (p.point j.castSucc).im) (b := (p.point j.succ).im) ht
  let C := cuts h r (p.point j.castSucc) (p.point j.succ)
  have hkC : k + 1 < C.length := hk
  have hstep : C[k] < C[k + 1] := (segmentCuts_sorted (levels h r) _ _).strictMono_get
    (show (⟨k, by omega⟩ : Fin C.length) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
  let u := (t - C[k]) / (C[k + 1] - C[k])
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hstep).le
    · rw [div_le_iff₀ (sub_pos.mpr hstep)]
      linarith
  have huval : AffineMap.lineMap C[k] C[k + 1] u = t := by
    rw [AffineMap.lineMap_apply_ring']
    dsimp [u]
    field_simp [sub_ne_zero.mpr (ne_of_gt hstep)]
    ring
  obtain ⟨q, hq, hfirst, hlast⟩ := sourceSamples_piece p h r j hk
  have hq' : q < (rawShear p h r d).segments := by
    rw [rawShear_segments]
    omega
  have heval := (rawShear_adjacent p h r d ⟨q, hq'⟩).1 u
  rw [hfirst, hlast] at heval
  have he : (rawShear p h r d).eval ⟨q, hq'⟩ u = plateauShear h r d (p.eval j t) := by
    rw [heval]
    change AffineMap.lineMap (plateauShear h r d (p.eval j C[k]))
      (plateauShear h r d (p.eval j C[k+1])) u = _
    exact (cut_eval hr d hk hu).symm.trans (congrArg (fun t => plateauShear h r d (p.eval j t))
        huval)
  exact he ▸ (rawShear p h r d).at_mem_support ⟨q, hq'⟩ hu

private theorem rawShear_support {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ) :
    (rawShear p h r d).support = plateauShear h r d '' p.support := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, t, ht, heq⟩ := ((rawShear p h r d).mem_support_iff z).mp hz
    obtain ⟨j, α, β, hα, hαβ, hβ, _hlevels, hj, _⟩ := rawShear_parameter hr p d i
    have hu : AffineMap.lineMap α β t ∈ Set.Icc (0 : ℝ) 1 := by
      have hm := lineMap_mem_segment ℝ α β ht
      rw [segment_eq_Icc hαβ.le] at hm
      exact ⟨hα.trans hm.1, hm.2.trans hβ⟩
    exact ⟨_, p.at_mem_support j hu, (hj t ht).symm.trans heq⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, t, ht, rfl⟩ := (p.mem_support_iff w).mp hw
    exact rawShear_contains hr p d j ht

private def untouched (p : Route) (h r : ℝ) : Prop :=
  (∀ i, (p.point i).im ≤ h - r) ∨ (∀ i, h + r ≤ (p.point i).im)

private theorem untouched_eval {h r : ℝ} (hr : 0 < r) {p : Route} (hp : untouched p h r)
    (d : ℝ) (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    plateauShear h r d (p.eval i t) = p.eval i t := by
  have him : (p.eval i t).im ∈ Set.Icc (min (p.point i.castSucc).im (p.point i.succ).im)
      (max (p.point i.castSucc).im (p.point i.succ).im) := by
    change Complex.imCLM.toLinearMap.toAffineMap (AffineMap.lineMap _ _ t) ∈ _
    rw [AffineMap.apply_lineMap, ← segment_eq_Icc']
    exact lineMap_mem_segment ℝ _ _ ht
  apply plateauShear_apply_outer hr d
  rcases hp with hp | hp
  · have hy : (p.eval i t).im ≤ h - r := him.2.trans (max_le (hp _) (hp _))
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hy : h + r ≤ (p.eval i t).im := (le_min (hp _) (hp _)).trans him.1
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem strictCuts_eq_empty_of_untouched {p : Route} {h r : ℝ} (hr : 0 < r)
    (hp : untouched p h r) (i : Fin p.segments) :
    strictCuts h r (p.point i.castSucc) (p.point i.succ) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  unfold strictCuts segmentInteriorCuts at ht
  split_ifs at ht with heq
  · simp at ht
  · obtain ⟨himage, hinterval⟩ := Finset.mem_filter.mp ht
    obtain ⟨y, hlevel, hparameter⟩ := Finset.mem_image.mp himage
    have ht : 0 < (y-(p.point i.castSucc).im)/((p.point i.succ).im-(p.point i.castSucc).im) ∧
        (y-(p.point i.castSucc).im)/((p.point i.succ).im-(p.point i.castSucc).im) < 1 := by
      rw [hparameter]
      exact hinterval
    let a := (p.point i.castSucc).im
    let b := (p.point i.succ).im
    have hne : b-a ≠ 0 := sub_ne_zero.mpr heq
    have hm : ((y-a)/(b-a))*(b-a) = y-a := div_mul_cancel₀ _ hne
    have hbetween : min a b < y ∧ y < max a b := by
      rcases lt_or_gt_of_ne hne with hn | hn
      · rw [min_eq_right (by linarith : b ≤ a), max_eq_left (by linarith : b ≤ a)]
        constructor <;> nlinarith [mul_neg_of_pos_of_neg ht.1 hn,
          mul_lt_mul_of_neg_right ht.2 hn]
      · rw [min_eq_left (by linarith : a ≤ b), max_eq_right (by linarith : a ≤ b)]
        constructor <;> nlinarith [mul_pos ht.1 hn, mul_lt_mul_of_pos_right ht.2 hn]
    have hylo : h-r ≤ y ∧ y ≤ h+r := by
      change y ∈ ({h-r,h-r/2,h+r/2,h+r} : Finset ℝ) at hlevel
      simp only [Finset.mem_insert, Finset.mem_singleton] at hlevel
      rcases hlevel with rfl | rfl | rfl | rfl <;> constructor <;> linarith
    rcases hp with hp | hp
    · have ha := hp i.castSucc
      have hb := hp i.succ
      have hh := hbetween.2
      have hmax : max a b ≤ h-r := max_le ha hb
      linarith
    · have ha := hp i.castSucc
      have hb := hp i.succ
      have hh := hbetween.1
      have hmin : h+r ≤ min a b := le_min ha hb
      linarith

namespace Route

open Classical in
/-- The finite route image under the concrete plateau shear. Nonpositive width is the
literal translated route. Zero displacement, and routes entirely in one outer closed
half-plane, return the literal original. Otherwise every indexed segment is split at its
strict internal height cuts and the actual image nodes are joined in source order. -/
noncomputable def plateauShear (p : Route) (h r d : ℝ) : Route :=
  if d = 0 then p else if r ≤ 0 then p.translate (d : ℂ) else
    if untouched p h r then p else rawShear p h r d

/-- Zero displacement does not leave collinear subdivision nodes behind. -/
theorem plateauShear_zero (p : Route) (h r : ℝ) : p.plateauShear h r 0 = p := by
  rw [plateauShear, ite_eq_left rfl]

/-- A whole node half-space, rather than merely the endpoints, suffices for literal retention. -/
theorem plateauShear_eq_self {p : Route} {h r : ℝ} (hr : 0 < r) (d : ℝ)
    (hp : (∀ i, (p.point i).im ≤ h - r) ∨ (∀ i, h + r ≤ (p.point i).im)) :
    p.plateauShear h r d = p := by
  unfold plateauShear
  split_ifs <;> simp_all [untouched, not_le.mpr hr]

/-- Each original segment contributes between one and five actual image pieces. -/
theorem segments_plateauShear (p : Route) (h r d : ℝ) :
    p.segments ≤ (p.plateauShear h r d).segments ∧
      (p.plateauShear h r d).segments ≤ 5 * p.segments := by
  unfold plateauShear
  split_ifs
  · constructor <;> omega
  · change p.segments ≤ p.segments ∧ p.segments ≤ 5 * p.segments
    constructor <;> omega
  · constructor <;> omega
  · rw [rawShear_segments]
    have hlen := sourceSamples_length p h r
    omega

/-- Exact piece count for a nonzero displacement and positive width: every old indexed
segment contributes one piece plus its distinct strict interior height-cut parameters.
Horizontal and degenerate segments have no cuts; untouched outer routes satisfy the same law. -/
theorem segments_plateauShear_eq {h r : ℝ} (hr : 0 < r) (p : Route) {d : ℝ} (hd : d ≠ 0) :
    let levels : Finset ℝ := {h-r, h-r/2, h+r/2, h+r}
    (p.plateauShear h r d).segments = ∑ i : Fin p.segments,
      let a := p.point i.castSucc
      let b := p.point i.succ
      let C : Finset ℝ := if b.im = a.im then ∅ else
        ((levels.image fun y => (y-a.im)/(b.im-a.im)).filter fun t => 0<t ∧ t<1)
      1+C.card := by
  change (p.plateauShear h r d).segments =
    Finset.univ.sum (fun (i : Fin p.segments) =>
      1+(strictCuts h r (p.point i.castSucc) (p.point i.succ)).card)
  rw [plateauShear, ite_eq_right hd, ite_eq_right (not_le.mpr hr)]
  by_cases hu : untouched p h r
  · rw [ite_eq_left hu]
    simp only [strictCuts_eq_empty_of_untouched hr hu, Finset.card_empty, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · rw [ite_eq_right hu, rawShear_segments, sourceSamples_length_eq_sum, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sourceBlock, List.length_map, List.length_dropLast,
      segmentCuts_length_eq, strictCuts]
    omega

/-- Actual continuum parameter transport. The old interval is strictly positive and lies
in `[0,1]`; the global nonlinear map is asserted only on CLOSED unit parameters. Both
original endpoint tags are preserved, including the two ends of a closed route. -/
theorem eval_plateauShear {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ)
    (i : Fin (p.plateauShear h r d).segments) :
    ∃ (j : Fin p.segments) (α β : ℝ), 0 ≤ α ∧ α < β ∧ β ≤ 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (p.plateauShear h r d).eval i t =
          Cslib.Polygonal.plateauShear h r d (p.eval j (AffineMap.lineMap α β t)) ∧
        ∀ b : Bool, (p.plateauShear h r d).AtEnd i t b ↔
          p.AtEnd j (AffineMap.lineMap α β t) b := by
  revert i
  by_cases hd : d = 0
  · subst d
    rw [plateauShear_zero]
    intro i
    refine ⟨i,0,1,le_rfl,zero_lt_one,le_rfl,?_⟩
    intro t ht
    simp only [AffineMap.lineMap_apply_ring', sub_zero, mul_one, add_zero,
      Cslib.Polygonal.plateauShear_apply, zero_mul, Complex.ofReal_zero, add_zero]
    exact ⟨True.intro, fun _ => True.intro⟩
  by_cases hu : untouched p h r
  · have hp : p.plateauShear h r d = p := by
      simp only [plateauShear, ite_eq_right hd, ite_eq_right (not_le.mpr hr), ite_eq_left hu]
    rw [hp]
    intro i
    refine ⟨i,0,1,le_rfl,zero_lt_one,le_rfl,?_⟩
    intro t ht
    simp only [AffineMap.lineMap_apply_ring', sub_zero, mul_one, add_zero]
    exact ⟨(untouched_eval hr hu d i ht).symm, fun _ => True.intro⟩
  have hp : p.plateauShear h r d = rawShear p h r d := by
    simp only [plateauShear, ite_eq_right hd, ite_eq_right (not_le.mpr hr), ite_eq_right hu]
  rw [hp]
  intro i
  obtain ⟨j,α,β,hα,hαβ,hβ,hn,he,hp⟩ := rawShear_parameter hr p d i
  refine ⟨j,α,β,hα,hαβ,hβ,fun t ht => ⟨he t ht,fun b => ?_⟩⟩
  rw [rawShear_atEnd p h r d i ht b, hp]
  rfl

/-- Either tagged endpoint is mapped by the actual shear, for every width and displacement. -/
theorem endpoint_plateauShear (p : Route) (h r d : ℝ) (b : Bool) :
    (p.plateauShear h r d).endpoint b =
      Cslib.Polygonal.plateauShear h r d (p.endpoint b) := by
  unfold plateauShear
  split_ifs with hd hn hu
  · simp only [hd, Cslib.Polygonal.plateauShear_apply, zero_mul, Complex.ofReal_zero, add_zero]
  · rw [endpoint_translate, Cslib.Polygonal.plateauShear_apply]
    change (d : ℂ) + p.endpoint b = p.endpoint b + (d * profile h r (p.endpoint b).im : ℝ)
    rw [profile_nonpos hn, mul_one, add_comm]
  · have he := untouched_eval (lt_of_not_ge hn) hu d (p.endSegment b)
      (Route.endTime_mem b (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num))
    simpa only [p.eval_near_end b 0, zero_smul, add_zero] using he.symm
  · exact rawShear_endpoint (lt_of_not_ge hn) p d b

/-- The complete continuous support is exactly the image of the original support.
This includes all intermediate points, horizontal or degenerate pieces and closed routes. -/
theorem support_plateauShear (p : Route) (h r d : ℝ) :
    (p.plateauShear h r d).support = Cslib.Polygonal.plateauShear h r d '' p.support := by
  unfold plateauShear
  split_ifs with hd hn hu
  · have he : Set.EqOn (Cslib.Polygonal.plateauShear h r d) id p.support := by
      intro z _
      simp only [hd, Cslib.Polygonal.plateauShear_apply, zero_mul, Complex.ofReal_zero,
        add_zero, id_eq]
    rw [Set.EqOn.image_eq he, Set.image_id]
  · rw [support_translate]
    apply Set.image_congr
    intro z _
    rw [Cslib.Polygonal.plateauShear_apply]
    change (d : ℂ) + z = z + (d * profile h r z.im : ℝ)
    rw [profile_nonpos hn, mul_one, add_comm]
  · have he : Set.EqOn (Cslib.Polygonal.plateauShear h r d) id p.support := by
      intro z hz
      obtain ⟨i, t, ht, rfl⟩ := (p.mem_support_iff z).mp hz
      exact untouched_eval (lt_of_not_ge hn) hu d i ht
    rw [Set.EqOn.image_eq he, Set.image_id]
  · exact rawShear_support (lt_of_not_ge hn) p d

/-- Shear subdivision preserves continuum simplicity, including first/last endpoint closure. -/
theorem IsSimple.plateauShear {p : Route} (hp : p.IsSimple) (h r d : ℝ) :
    (p.plateauShear h r d).IsSimple := by
  unfold Route.plateauShear
  split_ifs with hd hn hu
  · exact hp
  · exact hp.translate _
  · exact hp
  · exact rawShear_simple (lt_of_not_ge hn) hp d

end Route

private theorem shear_difference_flat {h r : ℝ} (hr : 0 < r) (d : ℝ) {a b : ℂ}
    (ha : |a.im - h| < r / 2 ∨ r < |a.im - h|)
    (hn : ∀ y ∈ levels h r, ¬(min a.im b.im < y ∧ y < max a.im b.im)) :
    plateauShear h r d b - plateauShear h r d a = b - a := by
  rcases ha with ha | ha
  · have ha' := abs_lt.mp ha
    have hb : |b.im - h| ≤ r / 2 := by
      rw [abs_le]
      constructor
      · by_contra hh
        have hlo : b.im < h - r / 2 := by linarith
        exact hn (h - r / 2) (by simp [levels])
          ⟨(min_le_right _ _).trans_lt hlo, by
            exact (by linarith [ha'.1] : h - r / 2 < a.im).trans_le (le_max_left _ _)⟩
      · by_contra hh
        have hhi : h + r / 2 < b.im := by linarith
        exact hn (h + r / 2) (by simp [levels])
          ⟨(min_le_left _ _).trans_lt (by linarith [ha'.2]),
            hhi.trans_le (le_max_right _ _)⟩
    rw [plateauShear_apply_inner hr d ha.le, plateauShear_apply_inner hr d hb,
      add_sub_add_right_eq_sub]
  · have habs := ha.le
    rcases lt_abs.mp ha with ha | ha
    · have hb : h + r ≤ b.im := by
        by_contra hh
        exact hn (h + r) (by simp [levels])
          ⟨(min_le_right _ _).trans_lt (lt_of_not_ge hh),
            (by linarith : h + r < a.im).trans_le (le_max_left _ _)⟩
      have hba : r ≤ |b.im - h| := by rw [abs_of_nonneg (by linarith)]; linarith
      rw [plateauShear_apply_outer hr d habs, plateauShear_apply_outer hr d hba]
    · have hb : b.im ≤ h - r := by
        by_contra hh
        exact hn (h - r) (by simp [levels])
          ⟨(min_le_left _ _).trans_lt (by linarith : a.im < h - r),
            (lt_of_not_ge hh).trans_le (le_max_right _ _)⟩
      have hba : r ≤ |b.im - h| := by rw [abs_of_nonpos (by linarith)]; linarith
      rw [plateauShear_apply_outer hr d habs,
        plateauShear_apply_outer hr d hba]

private theorem rawShear_germ {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ) (b : Bool)
    (ha : |(p.endpoint b).im - h| < r / 2 ∨ r < |(p.endpoint b).im - h|) :
    ∃ c : ℝ, 0 < c ∧ (rawShear p h r d).germ b = c • p.germ b := by
  let q := rawShear p h r d
  obtain ⟨j, α, β, hα, hαβ, hβ, hn, he, hp⟩ := rawShear_parameter hr p d (q.endSegment b)
  have hzero : q.AtEnd (q.endSegment b) (Route.endTime b 0) b := by
    rw [Route.AtEnd, q.position_near_end]
    cases b <;> simp
  have htzero := Route.endTime_mem b (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hpzero := (hp (Route.endTime b 0)).symm.trans
    ((rawShear_atEnd p h r d _ htzero b).mp hzero)
  cases b
  · have hj0 : j = 0 := by
      apply Fin.ext
      have hjnonneg := Nat.cast_nonneg (α := ℝ) j.val
      simp only [Route.endTime, Bool.false_eq_true, ↓reduceIte,
        AffineMap.lineMap_apply_zero, Route.position] at hpzero
      have hz : (j.val : ℝ) = 0 := by linarith
      change j.val = 0
      exact_mod_cast hz
    have hα0 : α = 0 := by
      simp only [hj0, Route.endTime, Bool.false_eq_true, ↓reduceIte,
        AffineMap.lineMap_apply_zero, Route.position, Fin.val_zero, Nat.cast_zero,
          zero_add] at hpzero
      exact hpzero
    have hn' : ∀ y ∈ levels h r, ¬(min p.start.im (p.eval 0 β).im < y ∧
        y < max p.start.im (p.eval 0 β).im) := by
      simpa only [hj0, hα0, Route.eval, AffineMap.lineMap_apply_zero, Route.start,
        Fin.castSucc_zero] using hn
    have hdif := shear_difference_flat hr d ha hn'
    refine ⟨β, by linarith, ?_⟩
    have hq1 := he 1 (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [AffineMap.lineMap_apply_one, hj0] at hq1
    change q.eval (q.endSegment false) (Route.endTime false 1) = _ at hq1
    rw [q.eval_near_end false 1,
      rawShear_endpoint hr p d false, one_smul] at hq1
    have hp1 := p.eval_near_end false β
    dsimp only [Route.endSegment, Route.endTime, Bool.false_eq_true, ↓reduceIte] at hp1
    change plateauShear h r d (p.eval 0 β) - plateauShear h r d p.start = _ at hdif
    have heval : q.germ false = plateauShear h r d (p.eval 0 β) -
        plateauShear h r d p.start := by
      change plateauShear h r d p.start + q.germ false = _ at hq1
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hq1)
    change plateauShear h r d (p.eval 0 β) - plateauShear h r d p.start = _ at hdif
    change p.eval 0 β = p.start + β • p.germ false at hp1
    rw [heval, hdif, hp1]
    simp only [Route.endpoint, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left]
  · have hβ1 : β = 1 := by
      have hjbound : (j.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast j.isLt
      simp only [Route.endTime, ↓reduceIte, sub_zero, AffineMap.lineMap_apply_one,
        Route.position] at hpzero
      linarith
    have hjlast : j = Fin.last p.bends := by
      apply Fin.ext
      simp only [Route.endTime, ↓reduceIte, sub_zero, AffineMap.lineMap_apply_one,
        Route.position, hβ1, Route.segments, Nat.cast_add, Nat.cast_one] at hpzero
      exact_mod_cast (show (j.val : ℝ) = p.bends by linarith)
    have hn' : ∀ y ∈ levels h r, ¬(min p.finish.im (p.eval (Fin.last p.bends) α).im < y ∧
        y < max p.finish.im (p.eval (Fin.last p.bends) α).im) := by
      simpa only [hjlast, hβ1, Route.eval, AffineMap.lineMap_apply_one, Route.finish,
        Fin.succ_last, Route.segments, min_comm, max_comm] using hn
    have hdif := shear_difference_flat hr d ha hn'
    refine ⟨1 - α, by linarith, ?_⟩
    have hq1 := he 0 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [AffineMap.lineMap_apply_zero, hjlast] at hq1
    have heval := q.eval_near_end true 1
    simp only [Route.endTime, ↓reduceIte, sub_self, one_smul] at heval
    change (rawShear p h r d).eval (q.endSegment true) 0 = _ at heval
    rw [hq1, rawShear_endpoint hr p d true] at heval
    have hp1 := p.eval_near_end true (1 - α)
    simp only [Route.endTime, Route.endSegment, ↓reduceIte, sub_sub_cancel] at hp1
    have heval' : q.germ true = plateauShear h r d (p.eval (Fin.last p.bends) α) -
        plateauShear h r d p.finish := by
      exact eq_sub_iff_add_eq.mpr (by simpa only [Route.endpoint, ↓reduceIte, add_comm] using
        heval.symm)
    change plateauShear h r d (p.eval (Fin.last p.bends) α) -
      plateauShear h r d p.finish = _ at hdif
    change p.eval (Fin.last p.bends) α = p.finish + (1-α) • p.germ true at hp1
    rw [heval', hdif, hp1]; simp only [Route.endpoint, ↓reduceIte, add_sub_cancel_left]

namespace Route

/-- At an endpoint strictly in a flat region, the actual outgoing germ is a positive
real multiple of the old one. The factor accounts for the first or last cut and therefore
need not equal one, including at inactive ends of a loop. -/
theorem germ_plateauShear {h r : ℝ} (hr : 0 < r) (p : Route) (d : ℝ) (b : Bool)
    (ha : |(p.endpoint b).im - h| < r / 2 ∨ r < |(p.endpoint b).im - h|) :
    ∃ c : ℝ, 0 < c ∧ (p.plateauShear h r d).germ b = c • p.germ b := by
  unfold plateauShear
  split_ifs with hd hn hu
  · exact ⟨1, zero_lt_one, (one_smul ℝ _).symm⟩
  · exact False.elim (not_le_of_gt hr hn)
  · exact ⟨1, zero_lt_one, (one_smul ℝ _).symm⟩
  · exact rawShear_germ hr p d b ha

end Route
end Cslib.Polygonal
