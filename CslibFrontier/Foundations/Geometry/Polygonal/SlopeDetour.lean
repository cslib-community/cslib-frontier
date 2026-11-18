/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Join
public import CslibFrontier.Foundations.Geometry.Polygonal.ParabolaChord
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Separating concurrent straight routes by two-piece detours

A finite family of distinct slopes through the origin admits arbitrarily small vertical
detours with the same ends. Every pair has exactly one transverse contact, in the open first
segments, and no three supports meet. An optional protected member remains literally its
original one-segment route. The other members use two segments through a perturbed middle point.

This is original finite coordinate geometry. Applying these local routes to the actual
reference drawing still requires indexed occurrence/slope injectivity, disjoint neighborhoods,
global route assembly and crossing-parity transport, tracked with placement and the
Hanani–Tutte/query objective in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).

## Main definitions

* `Cslib.Polygonal.Route.slopeDetour`: two segments through a prescribed middle height.

## Main results

* `Cslib.Polygonal.exists_slopeDetour_separation`: internally chosen heights separate a finite
  concurrent family, with an optional literal protected line and an arbitrary tube tolerance.
-/

public section

namespace Cslib.Polygonal

namespace Route

/-- Join the two slope-s endpoints through a middle point of height d. -/
@[expose] def slopeDetour (r s d : ℝ) : Route :=
  (line ⟨-r, -r * s⟩ ⟨0, d⟩).append ⟨r, r * s⟩

/-- The detour starts at the original left endpoint. -/
@[simp] theorem start_slopeDetour (r s d : ℝ) :
    (slopeDetour r s d).start = ⟨-r, -r * s⟩ := rfl

/-- The detour finishes at the original right endpoint. -/
@[simp] theorem finish_slopeDetour (r s d : ℝ) :
    (slopeDetour r s d).finish = ⟨r, r * s⟩ := rfl

/-- Both actual pieces retain their full real affine parameter. -/
theorem eval_slopeDetour (r s d : ℝ) (i : Fin (slopeDetour r s d).segments) (t : ℝ) :
    (slopeDetour r s d).eval i t =
      if i.val = 0 then AffineMap.lineMap ⟨-r, -r * s⟩ ⟨0, d⟩ t
      else AffineMap.lineMap ⟨0, d⟩ ⟨r, r * s⟩ t := by
  have hi2 : i.val < 2 := i.isLt
  rcases (show i.val = 0 ∨ i.val = 1 from by omega) with hi | hi
  · have he : i = (0 : Fin 2) := Fin.ext hi
    subst i
    exact eval_append_castSucc _ _ 0 t
  · have he : i = (1 : Fin 2) := Fin.ext hi
    subst i
    exact eval_append_last _ _ t

end Route

open Route

private def member (r s d : ℝ) (keep : Bool) : Route :=
  if keep then line ⟨-r, -r * s⟩ ⟨r, r * s⟩ else slopeDetour r s d

private def height (a c μ s : ℝ) : ℝ := μ * ((s - a) ^ 2 + c * (s - a))

private theorem height_sub (a c μ s t : ℝ) :
    height a c μ s - height a c μ t = (s - t) * (μ * (s + t - 2 * a + c)) := by
  dsimp [height]
  ring

private theorem member_ends (r s d : ℝ) (keep : Bool) :
    (member r s d keep).start = ⟨-r, -r * s⟩ ∧
      (member r s d keep).finish = ⟨r, r * s⟩ := by
  cases keep <;> simp [member]

private theorem member_simple {r : ℝ} (hr : 0 < r) (s d : ℝ) (keep : Bool) :
    (member r s d keep).IsSimple := by
  have hleft : (⟨-r, -r * s⟩ : ℂ) ≠ ⟨0, d⟩ := by
    intro h
    have := congrArg Complex.re h
    change -r = 0 at this
    linarith
  cases keep
  · apply IsSimple.append (isSimple_line hleft)
    · intro h
      have := congrArg Complex.re h
      change 0 = r at this
      linarith
    · intro i u v hu hv heq
      rw [eval_line] at heq
      have hreal := congrArg Complex.re heq
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
        smul_eq_mul, finish_line, mul_zero, add_zero, zero_add] at hreal
      have hprod : r * (u - 1 - v) = 0 := by nlinarith only [hreal]
      have hparam := (mul_eq_zero.mp hprod).resolve_left hr.ne'
      have hu1 : u = 1 := by linarith [hu.2, hv.1]
      have hv0 : v = 0 := by linarith [hu.2, hv.1]
      exact Or.inl ⟨(atEnd_line_iff _ _ i u true).mpr hu1, hv0⟩
  · apply isSimple_line
    intro h
    have := congrArg Complex.re h
    change -r = r at this
    linarith

private theorem member_support {r s d : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) {z : ℂ} (hz : z ∈ (member r s d keep).support) :
    z.re ∈ Set.Icc (-r) r ∧ z.im = s * z.re + d * (1 - |z.re| / r) := by
  cases keep
  · change z ∈ (slopeDetour r s d).support at hz
    obtain ⟨i, t, ht, rfl⟩ := ((slopeDetour r s d).mem_support_iff z).mp hz
    rw [eval_slopeDetour]
    split_ifs with hi
    · have hx : -r ≤ (1 - t) * -r ∧ (1 - t) * -r ≤ 0 := by
        constructor <;> nlinarith [ht.1, ht.2]
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_zero,
        add_zero]
      refine ⟨⟨hx.1, hx.2.trans hr.le⟩, ?_⟩
      rw [abs_of_nonpos hx.2]
      field_simp [hr.ne']
      ring
    · have hx : 0 ≤ t * r ∧ t * r ≤ r := by constructor <;> nlinarith [ht.1, ht.2]
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_zero,
        zero_add]
      refine ⟨⟨by linarith [hx.1], hx.2⟩, ?_⟩
      rw [abs_of_nonneg hx.1]
      field_simp [hr.ne']
      ring
  · have hd := hkeep rfl
    change z ∈ (line (⟨-r, -r * s⟩ : ℂ) ⟨r, r * s⟩).support at hz
    obtain ⟨i, t, ht, rfl⟩ :=
      ((line (⟨-r, -r * s⟩ : ℂ) ⟨r, r * s⟩).mem_support_iff z).mp hz
    rw [eval_line]
    simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, hd,
      zero_mul, add_zero]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith [ht.1, ht.2]

private theorem member_tube {r s d ε : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) (hd : |d| < ε)
    {z : ℂ} (hz : z ∈ (member r s d keep).support) :
    z.re ∈ Set.Icc (-r) r ∧ |z.im - s * z.re| < ε := by
  obtain ⟨hx, hy⟩ := member_support hr hkeep hz
  have habs : |z.re| ≤ r := abs_le.mpr hx
  have hw : 0 ≤ 1 - |z.re| / r ∧ 1 - |z.re| / r ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr ((div_le_one hr).mpr habs)
    · linarith [div_nonneg (abs_nonneg z.re) hr.le]
  refine ⟨hx, ?_⟩
  rw [hy, add_sub_cancel_left, abs_mul, abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_right (abs_nonneg d) hw.2).trans_lt hd

private theorem member_first {r s d x : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) (hx : x ∈ Set.Ioo (-r) 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (member r s d keep).eval 0 t = ⟨x, s * x + d * (1 + x / r)⟩ := by
  cases keep
  · refine ⟨(x + r) / r, ⟨div_pos (by linarith [hx.1]) hr,
      (div_lt_one hr).mpr (by linarith [hx.2])⟩, ?_⟩
    rw [show member r s d false = slopeDetour r s d from rfl, eval_slopeDetour]
    simp only [Fin.val_zero, ↓reduceIte, AffineMap.lineMap_apply_module,
      Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    constructor <;> field_simp [hr.ne'] <;> ring
  · have hd := hkeep rfl
    refine ⟨(x + r) / (2 * r), ⟨div_pos (by linarith [hx.1]) (by linarith),
      (div_lt_one (by linarith : 0 < 2 * r)).mpr (by linarith [hx.2])⟩, ?_⟩
    rw [show member r s d true = line ⟨-r, -r * s⟩ ⟨r, r * s⟩ from rfl, eval_line]
    simp only [hd, zero_mul, add_zero, AffineMap.lineMap_apply_module, Complex.ext_iff,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    constructor <;> field_simp [hr.ne'] <;> ring

private theorem member_first_vector (r s d : ℝ) (keep : Bool)
    (hkeep : keep = true → d = 0) :
    (member r s d keep).germ false =
      (if keep then (2 : ℝ) else 1) • (⟨r, r * s + d⟩ : ℂ) := by
  cases keep
  · simp only [member, Bool.false_eq_true, ↓reduceIte, slopeDetour, germ_append,
      germ_line, one_smul]
    apply Complex.ext <;> simp [add_comm]
  · have hd := hkeep rfl
    simp only [member, ↓reduceIte, germ_line, hd, add_zero]
    apply Complex.ext <;> simp [Complex.real_smul, two_mul]

private theorem contact_abscissa {r s t d e q x y : ℝ} (hr : 0 < r) (hst : s ≠ t)
    (hq : 0 < q) (hd : d - e = (s - t) * q) (hx : x ∈ Set.Icc (-r) r)
    (hs : y = s * x + d * (1 - |x| / r))
    (ht : y = t * x + e * (1 - |x| / r)) : x = -r * q / (r + q) := by
  have hprod : (s - t) * (x + q * (1 - |x| / r)) = 0 := by
    calc
      _ = (s - t) * x + (d - e) * (1 - |x| / r) := by rw [hd]; ring
      _ = 0 := by linarith
  have hzero := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hst)
  have hneg : x < 0 := by
    by_contra h
    have hnonneg : 0 ≤ x := not_lt.mp h
    rw [abs_of_nonneg hnonneg] at hzero
    have hw : 0 ≤ 1 - x / r := sub_nonneg.mpr ((div_le_one hr).mpr hx.2)
    have hx0 : x = 0 := by nlinarith [mul_nonneg hq.le hw]
    rw [hx0] at hzero
    simp only [zero_div, sub_zero, mul_one, zero_add] at hzero
    exact hq.ne' hzero
  rw [abs_of_neg hneg] at hzero
  apply (eq_div_iff (by linarith : r + q ≠ 0)).mpr
  field_simp [hr.ne'] at hzero
  nlinarith only [hzero]

private theorem pair_separation {r s t d e q : ℝ} (hr : 0 < r) (hst : s ≠ t)
    (hq : 0 < q) (hqr : q < r / 2) (hd : d - e = (s - t) * q)
    (keep keep' : Bool) (hk : keep = true → d = 0) (hk' : keep' = true → e = 0) :
    (∃! z : ℂ, z ∈ (member r s d keep).support ∧ z ∈ (member r t e keep').support) ∧
      (∀ z : ℂ, z ∈ (member r s d keep).support →
        z ∈ (member r t e keep').support →
        -r / 3 < z.re ∧ z.re < 0 ∧
          ∃ u v : ℝ, u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
            (member r s d keep).eval 0 u = z ∧ (member r t e keep').eval 0 v = z) ∧
      ((member r s d keep).germ false).re * ((member r t e keep').germ false).im -
        ((member r s d keep).germ false).im * ((member r t e keep').germ false).re ≠ 0 := by
  let x := -r * q / (r + q)
  let z : ℂ := ⟨x, s * x + d * (1 + x / r)⟩
  have hrq : 0 < r + q := add_pos hr hq
  have hx : -r / 3 < x ∧ x < 0 := by
    constructor
    · apply (lt_div_iff₀ hrq).mpr
      nlinarith [mul_pos hr (by linarith : 0 < r - 2 * q)]
    · exact div_neg_of_neg_of_pos (by nlinarith [mul_pos hr hq]) hrq
  have hxr : x ∈ Set.Ioo (-r) 0 := ⟨by linarith [hx.1], hx.2⟩
  have hroot : s * x + d * (1 + x / r) = t * x + e * (1 + x / r) := by
    have he : (s - t) * x + (d - e) * (1 + x / r) = 0 := by
      rw [hd]
      dsimp [x]
      field_simp [hr.ne', hrq.ne']
      ring
    linarith
  obtain ⟨u, hu, hue⟩ := member_first (s := s) hr hk hxr
  obtain ⟨v, hv, hve⟩ := member_first (s := t) hr hk' hxr
  have hz : z ∈ (member r s d keep).support ∧ z ∈ (member r t e keep').support := by
    constructor
    · have hmem := (member r s d keep).at_mem_support 0 ⟨hu.1.le, hu.2.le⟩
      rw [hue] at hmem
      exact hmem
    · rw [show z = (⟨x, t * x + e * (1 + x / r)⟩ : ℂ) from Complex.ext rfl hroot]
      exact hve ▸ (member r t e keep').at_mem_support 0 ⟨hv.1.le, hv.2.le⟩
  have common {w : ℂ} (hw : w ∈ (member r s d keep).support)
      (hw' : w ∈ (member r t e keep').support) : w = z := by
    obtain ⟨hwx, hwy⟩ := member_support hr hk hw
    obtain ⟨_, hwy'⟩ := member_support hr hk' hw'
    have hwre := contact_abscissa hr hst hq hd hwx hwy hwy'
    apply Complex.ext hwre
    rw [hwy, hwre, abs_of_neg hx.2]
    change s * x + d * (1 - -x / r) = s * x + d * (1 + x / r)
    ring
  refine ⟨⟨z, hz, fun w hw => common hw.1 hw.2⟩, ?_, ?_⟩
  · intro w hw hw'
    rw [common hw hw']
    exact ⟨hx.1, hx.2, u, v, hu, hv, hue, hve.trans (Complex.ext rfl hroot.symm)⟩
  · rw [member_first_vector r s d keep hk, member_first_vector r t e keep' hk']
    have he : e - d = (t - s) * q := by linarith [hd]
    let m : ℝ := if keep then 2 else 1
    let n : ℝ := if keep' then 2 else 1
    change (m • (⟨r, r * s + d⟩ : ℂ)).re * (n • (⟨r, r * t + e⟩ : ℂ)).im -
      (m • (⟨r, r * s + d⟩ : ℂ)).im * (n • (⟨r, r * t + e⟩ : ℂ)).re ≠ 0
    have hdet :
        (m • (⟨r, r * s + d⟩ : ℂ)).re * (n • (⟨r, r * t + e⟩ : ℂ)).im -
          (m • (⟨r, r * s + d⟩ : ℂ)).im * (n • (⟨r, r * t + e⟩ : ℂ)).re =
          m * n * r * (t - s) * (r + q) := by
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
      calc
        _ = m * n * r * ((t - s) * r + (e - d)) := by ring
        _ = _ := by rw [he]; ring
    rw [hdet]
    have hk0 : m ≠ 0 := by cases keep <;> norm_num [m]
    have hk'0 : n ≠ 0 := by cases keep' <;> norm_num [n]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hk0 hk'0) hr.ne')
      (sub_ne_zero.mpr hst.symm)) hrq.ne'

private noncomputable def lift (a c μ : ℝ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := ⟨z.re, μ * (z.im + (c - 2 * a) * z.re + a ^ 2 - c * a)⟩
  linear :=
    { toFun := fun z => ⟨z.re, μ * (z.im + (c - 2 * a) * z.re)⟩
      map_add' := by intro z w; apply Complex.ext <;> simp; ring
      map_smul' := by intro t z; apply Complex.ext <;> simp [Complex.real_smul]; ring }
  map_vadd' := by intro z w; apply Complex.ext <;> simp; ring

private theorem lift_parabola (a c μ s : ℝ) :
    lift a c μ (parabolaPoint s) = ⟨s, height a c μ s⟩ := by
  simp only [lift, AffineMap.coe_mk, parabolaPoint, height]
  apply Complex.ext
  · rfl
  · change μ * (s ^ 2 + (c - 2 * a) * s + a ^ 2 - c * a) =
      μ * ((s - a) ^ 2 + c * (s - a))
    ring

private theorem lift_injective {a c μ : ℝ} (hμ : μ ≠ 0) :
    Function.Injective (lift a c μ) := by
  intro z w h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  change z.re = w.re at hre
  change μ * (z.im + (c - 2 * a) * z.re + a ^ 2 - c * a) =
    μ * (w.im + (c - 2 * a) * w.re + a ^ 2 - c * a) at him
  have := mul_left_cancel₀ hμ him
  exact Complex.ext hre (by rw [hre] at this; linarith)

private theorem no_middle {a c μ w x y s t u : ℝ} (hμ : μ ≠ 0) (hw : w ≠ 0)
    (hst : s < t) (htu : t < u)
    (hs : y = s * x + w * height a c μ s)
    (ht : y = t * x + w * height a c μ t)
    (hu : y = u * x + w * height a c μ u) : False := by
  let v := (t - s) / (u - s)
  have hus : 0 < u - s := by linarith
  have hv : v ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos (sub_pos.mpr hst) hus).le, ((div_lt_one hus).mpr (by linarith)).le⟩
  have hinterp : (1 - v) * s + v * u = t := by
    dsimp [v]
    field_simp [hus.ne']
    ring
  have hd : (1 - v) * height a c μ s + v * height a c μ u = height a c μ t := by
    have hzero : w * ((1 - v) * height a c μ s + v * height a c μ u -
        height a c μ t) = 0 := by
      calc
        _ = (1 - v) * (w * height a c μ s) + v * (w * height a c μ u) -
            w * height a c μ t := by ring
        _ = (1 - v) * (y - s * x) + v * (y - u * x) - (y - t * x) := by
          rw [show w * height a c μ s = y - s * x from by linarith,
            show w * height a c μ u = y - u * x from by linarith,
            show w * height a c μ t = y - t * x from by linarith]
        _ = -x * ((1 - v) * s + v * u - t) := by ring
        _ = 0 := by rw [hinterp]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hw)
  have hmap : lift a c μ (AffineMap.lineMap (parabolaPoint s) (parabolaPoint u) v) =
      lift a c μ (parabolaPoint t) := by
    rw [AffineMap.apply_lineMap, lift_parabola, lift_parabola, lift_parabola]
    apply Complex.ext
    · simpa only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
        smul_eq_mul] using hinterp
    · simpa only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im,
        smul_eq_mul] using hd
  have hpoint := lift_injective hμ hmap
  have hmem := lineMap_mem_segment ℝ (parabolaPoint s) (parabolaPoint u) hv
  rw [hpoint] at hmem
  rcases (parabolaPoint_mem_segment_iff s u t).mp hmem with h | h
  · exact hst.ne' h
  · exact htu.ne h

private theorem no_three {a c μ w x y s t u : ℝ} (hμ : μ ≠ 0) (hw : w ≠ 0)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : y = s * x + w * height a c μ s)
    (ht : y = t * x + w * height a c μ t)
    (hu : y = u * x + w * height a c μ u) : False := by
  rcases lt_or_gt_of_ne hst with hst | hts
  · rcases lt_or_gt_of_ne htu with htu | hut
    · exact no_middle hμ hw hst htu hs ht hu
    · rcases lt_or_gt_of_ne hsu with hsu | hus
      · exact no_middle hμ hw hsu hut hs hu ht
      · exact no_middle hμ hw hus hst hu hs ht
  · rcases lt_or_gt_of_ne hsu with hsu | hus
    · exact no_middle hμ hw hts hsu ht hs hu
    · rcases lt_or_gt_of_ne htu with htu | hut
      · exact no_middle hμ hw htu hus ht hu hs
      · exact no_middle hμ hw hut hts hu ht hs

open Classical in
/-- Distinct finite slopes admit small actual detours with one transverse interior contact
per pair and no triple contact. The optional protected route remains literally one segment.
No neighborhood, placement or global parity-preservation hypothesis is supplied. -/
theorem exists_slopeDetour_separation {ι : Type*} [Finite ι]
    (s : ι → ℝ) (hs : Function.Injective s) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (fixedIndex : Option ι) :
    ∃ d : ι → ℝ,
      let R : ι → Route := fun i =>
        if fixedIndex = some i then line ⟨-r, -r * s i⟩ ⟨r, r * s i⟩
        else slopeDetour r (s i) (d i)
      (∀ i, (R i).start = ⟨-r, -r * s i⟩ ∧ (R i).finish = ⟨r, r * s i⟩ ∧
        (R i).IsSimple ∧ ∀ z ∈ (R i).support,
          z.re ∈ Set.Icc (-r) r ∧ |z.im - s i * z.re| < ε) ∧
      (∀ f, fixedIndex = some f → d f = 0 ∧
        R f = line ⟨-r, -r * s f⟩ ⟨r, r * s f⟩) ∧
      (∀ i j, i ≠ j → ∃! z : ℂ, z ∈ (R i).support ∧ z ∈ (R j).support) ∧
      (∀ i j, i ≠ j → ∀ z : ℂ, z ∈ (R i).support → z ∈ (R j).support →
        -r / 3 < z.re ∧ z.re < 0 ∧
          ∃ u v : ℝ, u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
            (R i).eval 0 u = z ∧ (R j).eval 0 v = z) ∧
      (∀ i j, i ≠ j →
        ((R i).germ false).re * ((R j).germ false).im -
          ((R i).germ false).im * ((R j).germ false).re ≠ 0) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ z : ℂ,
        z ∈ (R i).support → z ∈ (R j).support → z ∉ (R k).support) := by
  classical
  let := Fintype.ofFinite ι
  let a := fixedIndex.elim 0 s
  let M := ∑ i, |s i - a|
  let c := 2 * M + 1
  let B := M ^ 2 + c * M
  let Q := 4 * M + 1
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc : 0 < c := by dsimp [c]; linarith
  have hB : 0 ≤ B := add_nonneg (sq_nonneg M) (mul_nonneg hc.le hM)
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hbound : 0 < min (ε / (B + 1)) (r / (2 * (Q + 1))) := by positivity
  obtain ⟨μ, hμ, hμlt⟩ := exists_between hbound
  have hμε : μ * (B + 1) < ε :=
    (lt_div_iff₀ (by linarith : 0 < B + 1)).mp ((lt_min_iff.mp hμlt).1)
  have hμr : μ * (2 * (Q + 1)) < r :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (Q + 1))).mp ((lt_min_iff.mp hμlt).2)
  let d := fun i => height a c μ (s i)
  let keep := fun i => decide (fixedIndex = some i)
  let R := fun i => member r (s i) (d i) (keep i)
  have hM_i (i : ι) : |s i - a| ≤ M :=
    Finset.single_le_sum (fun j _ => abs_nonneg (s j - a)) (Finset.mem_univ i)
  have hd (i : ι) : |d i| < ε := by
    have hz := hM_i i
    have hsq : (s i - a) ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (s i - a)) hM).mpr hz
    calc
      |d i| = μ * |(s i - a) ^ 2 + c * (s i - a)| := by
        simp only [d, height, abs_mul, abs_of_pos hμ]
      _ ≤ μ * ((s i - a) ^ 2 + c * |s i - a|) := by
        apply mul_le_mul_of_nonneg_left _ hμ.le
        calc
          _ ≤ |(s i - a) ^ 2| + |c * (s i - a)| := abs_add_le _ _
          _ = _ := by rw [abs_of_nonneg (sq_nonneg (s i - a)), abs_mul, abs_of_pos hc]
      _ ≤ μ * B := by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_left hz hc.le]
      _ < ε := by nlinarith
  have hkeep (i : ι) : keep i = true → d i = 0 := by
    intro hi
    have hi' : fixedIndex = some i := of_decide_eq_true hi
    simp [d, height, a, hi']
  have hpair (i j : ι) (hij : i ≠ j) :
      (∃! z : ℂ, z ∈ (R i).support ∧ z ∈ (R j).support) ∧
        (∀ z : ℂ, z ∈ (R i).support → z ∈ (R j).support →
          -r / 3 < z.re ∧ z.re < 0 ∧
            ∃ u v : ℝ, u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
              (R i).eval 0 u = z ∧ (R j).eval 0 v = z) ∧
        ((R i).germ false).re * ((R j).germ false).im -
          ((R i).germ false).im * ((R j).germ false).re ≠ 0 := by
    let q := μ * (s i + s j - 2 * a + c)
    have hi := abs_le.mp (hM_i i)
    have hj := abs_le.mp (hM_i j)
    have hfactor : 1 ≤ s i + s j - 2 * a + c ∧
        s i + s j - 2 * a + c ≤ Q := by dsimp [c, Q]; constructor <;> linarith
    have hq : 0 < q := by dsimp [q]; nlinarith [hfactor.1]
    have hqr : q < r / 2 := by
      have hle := mul_le_mul_of_nonneg_left hfactor.2 hμ.le
      dsimp [q]
      nlinarith
    exact pair_separation hr (fun h => hij (hs h)) hq hqr
      (height_sub a c μ (s i) (s j)) (keep i) (keep j) (hkeep i) (hkeep j)
  refine ⟨d, ?_⟩
  have hR : (fun i =>
      if fixedIndex = some i then line ⟨-r, -r * s i⟩ ⟨r, r * s i⟩
      else slopeDetour r (s i) (d i)) = R := by
    funext i
    simp [R, member, keep]
  rw [hR]
  dsimp only
  refine ⟨?_, ?_, fun i j hij => (hpair i j hij).1,
    fun i j hij => (hpair i j hij).2.1, fun i j hij => (hpair i j hij).2.2, ?_⟩
  · intro i
    exact ⟨(member_ends r (s i) (d i) (keep i)).1,
      (member_ends r (s i) (d i) (keep i)).2, member_simple hr _ _ _,
      fun _ hz => member_tube hr (hkeep i) (hd i) hz⟩
  · intro f hf
    have hk : keep f = true := by simp [keep, hf]
    exact ⟨hkeep f hk, by simp [R, member, hk]⟩
  · intro i j k hij hik hjk z hi hj hk
    obtain ⟨hx, hz0, _⟩ := (hpair i j hij).2.1 z hi hj
    have hw : 0 < 1 - |z.re| / r := by
      rw [abs_of_neg hz0]
      have hzlow : -r < z.re := by linarith
      exact sub_pos.mpr ((div_lt_one hr).mpr (by linarith))
    obtain ⟨_, hi'⟩ := member_support hr (hkeep i) hi
    obtain ⟨_, hj'⟩ := member_support hr (hkeep j) hj
    obtain ⟨_, hk'⟩ := member_support hr (hkeep k) hk
    exact no_three hμ.ne' hw.ne' (fun h => hij (hs h)) (fun h => hik (hs h))
      (fun h => hjk (hs h))
      (by simpa only [d, mul_comm (height a c μ (s i))] using hi')
      (by simpa only [d, mul_comm (height a c μ (s j))] using hj')
      (by simpa only [d, mul_comm (height a c μ (s k))] using hk')

end Cslib.Polygonal
