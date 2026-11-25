/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Translation
public import Mathlib.Topology.Homeomorph.Lemmas
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.CutTransport
import CslibFrontier.Tactic.LinarithCast
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

private theorem shear_lineMap (h : ℝ) {r : ℝ} (hr : 0 < r) (d : ℝ) (a b : ℂ)
    (hn : ∀ y ∈ levels h r, y ∉ Set.Ioo (min a.im b.im) (max a.im b.im))
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
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

private noncomputable abbrev rawShear (p : Route) (h r d : ℝ) : Route :=
  p.mapAtCuts (levels h r) Complex.imCLM.toLinearMap.toAffineMap (plateauShear h r d)

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
  · have hbounds := segments_mapAtCuts p (levels h r) Complex.imCLM.toLinearMap.toAffineMap
      (Cslib.Polygonal.plateauShear h r d)
    have hcard : (levels h r).card ≤ 4 := Finset.card_le_four
    exact ⟨hbounds.1, hbounds.2.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hcard 1))⟩

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
  · rw [ite_eq_right hu]
    exact segments_mapAtCuts_eq p (levels h r) Complex.imCLM.toLinearMap.toAffineMap
      (Cslib.Polygonal.plateauShear h r d)

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
  obtain ⟨j, α, β, hα, hαβ, hβ, _, he⟩ :=
    eval_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap) (shear_lineMap h hr d) p i
  exact ⟨j, α, β, hα, hαβ, hβ, he⟩

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
  · exact endpoint_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h (lt_of_not_ge hn) d) p b

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
  · exact support_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h (lt_of_not_ge hn) d) p

/-- Shear subdivision preserves continuum simplicity, including first/last endpoint closure. -/
theorem IsSimple.plateauShear {p : Route} (hp : p.IsSimple) (h r d : ℝ) :
    (p.plateauShear h r d).IsSimple := by
  unfold Route.plateauShear
  split_ifs with hd hn hu
  · exact hp
  · exact hp.translate _
  · exact hp
  · exact IsSimple.mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h (lt_of_not_ge hn) d) hp
      (Cslib.Polygonal.plateauShear h r d).injective

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
  obtain ⟨j, α, β, hα, hαβ, hβ, hn, he⟩ :=
    Route.eval_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h hr d) p (q.endSegment b)
  change ∀ y ∈ levels h r, ¬(min (p.eval j α).im (p.eval j β).im < y ∧
    y < max (p.eval j α).im (p.eval j β).im) at hn
  have hzero : q.AtEnd (q.endSegment b) (Route.endTime b 0) b := by
    rw [Route.AtEnd, q.position_near_end]
    cases b <;> simp
  have htzero := Route.endTime_mem b (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hpzero := ((he (Route.endTime b 0) htzero).2 b).mp hzero
  change p.position j (AffineMap.lineMap α β (Route.endTime b 0)) =
    (if b then (p.segments : ℝ) else 0) at hpzero
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
    have hq1 := (he 1 (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)).1
    rw [AffineMap.lineMap_apply_one, hj0] at hq1
    change q.eval (q.endSegment false) (Route.endTime false 1) = _ at hq1
    have hstart := Route.endpoint_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h hr d) p false
    rw [q.eval_near_end false 1, hstart, one_smul] at hq1
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
      simp only [Route.endTime, ↓reduceIte, sub_zero, AffineMap.lineMap_apply_one,
        Route.position] at hpzero
      cast_linarith [j.isLt]
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
    have hq1 := (he 0 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)).1
    rw [AffineMap.lineMap_apply_zero, hjlast] at hq1
    have heval := q.eval_near_end true 1
    simp only [Route.endTime, ↓reduceIte, sub_self, one_smul] at heval
    change (rawShear p h r d).eval (q.endSegment true) 0 = _ at heval
    have hfinish := Route.endpoint_mapAtCuts (c := Complex.imCLM.toLinearMap.toAffineMap)
      (shear_lineMap h hr d) p true
    rw [hq1, hfinish] at heval
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
