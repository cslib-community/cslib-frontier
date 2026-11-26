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
import CslibFrontier.Foundations.Geometry.Polygonal.CoordinateOrder
import Mathlib.Tactic.FinCases
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
  fin_cases i
  · exact eval_append_castSucc _ _ 0 t
  · exact eval_append_last _ _ t

end Route

open Route

private def member (r s d : ℝ) (keep : Bool) : Route :=
  if keep then line ⟨-r, -r * s⟩ ⟨r, r * s⟩ else slopeDetour r s d

private def height (a c μ s : ℝ) : ℝ := μ * ((s - a) ^ 2 + c * (s - a))

private theorem height_sub (a c μ s t : ℝ) :
    height a c μ s - height a c μ t = (s - t) * (μ * (s + t - 2 * a + c)) := by
  dsimp [height]; ring

private theorem member_ends (r s d : ℝ) (keep : Bool) :
    (member r s d keep).start = ⟨-r, -r * s⟩ ∧
      (member r s d keep).finish = ⟨r, r * s⟩ := by
  cases keep <;> simp [member]

private theorem member_simple {r : ℝ} (hr : 0 < r) (s d : ℝ) (keep : Bool) :
    (member r s d keep).IsSimple := by
  cases keep <;> refine isSimple_of_strictMono_re (Fin.strictMono_iff_lt_succ.mpr fun i => ?_) <;>
    fin_cases i
  exacts [show -r < (0 : ℝ) by linarith, show (0 : ℝ) < r from hr, show -r < r by linarith]

private theorem member_support {r s d : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) {z : ℂ} (hz : z ∈ (member r s d keep).support) :
    z.re ∈ Set.Icc (-r) r ∧ z.im = s * z.re + d * (1 - |z.re| / r) := by
  cases keep
  · obtain ⟨i, t, ht, rfl⟩ := ((slopeDetour r s d).mem_support_iff z).mp hz
    rw [eval_slopeDetour]
    split_ifs with hi
    · have hx : -r ≤ (1 - t) * -r ∧ (1 - t) * -r ≤ 0 := by
        constructor <;> nlinarith only [ht.1, ht.2, hr]
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_zero,
        add_zero]
      refine ⟨⟨hx.1, hx.2.trans hr.le⟩, ?_⟩
      rw [abs_of_nonpos hx.2]
      field_simp [hr.ne']; ring
    · have hx : 0 ≤ t * r ∧ t * r ≤ r := by constructor <;> nlinarith only [ht.1, ht.2, hr]
      simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
        Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_zero,
        zero_add]
      refine ⟨⟨by linarith only [hr, hx.1], hx.2⟩, ?_⟩
      rw [abs_of_nonneg hx.1]
      field_simp [hr.ne']; ring
  · obtain ⟨i, t, ht, rfl⟩ := ((line (⟨-r, -r * s⟩ : ℂ) ⟨r, r * s⟩).mem_support_iff z).mp hz
    simp only [eval_line, AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, hkeep rfl, zero_mul, add_zero]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith only [ht.1, ht.2, hr]

private theorem member_tube {r s d ε : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) (hd : |d| < ε)
    {z : ℂ} (hz : z ∈ (member r s d keep).support) :
    z.re ∈ Set.Icc (-r) r ∧ |z.im - s * z.re| < ε := by
  obtain ⟨hx, hy⟩ := member_support hr hkeep hz
  have hw : 0 ≤ 1 - |z.re| / r := sub_nonneg.mpr ((div_le_one hr).mpr (abs_le.mpr hx))
  refine ⟨hx, ?_⟩
  rw [hy, add_sub_cancel_left, abs_mul, abs_of_nonneg hw]
  exact (mul_le_of_le_one_right (abs_nonneg d) (sub_le_self _ (by positivity))).trans_lt hd

private theorem member_first {r s d x : ℝ} {keep : Bool} (hr : 0 < r)
    (hkeep : keep = true → d = 0) (hx : x ∈ Set.Ioo (-r) 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (member r s d keep).eval 0 t = ⟨x, s * x + d * (1 + x / r)⟩ := by
  cases keep
  · refine ⟨(x + r) / r, ⟨div_pos (by linarith [hx.1]) hr,
      (div_lt_one hr).mpr (by linarith [hx.2])⟩, ?_⟩
    change (slopeDetour r s d).eval 0 _ = _
    simp only [eval_slopeDetour, Fin.val_zero, ↓reduceIte, AffineMap.lineMap_apply_module,
      Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    constructor <;> field_simp [hr.ne'] <;> ring
  · refine ⟨(x + r) / (2 * r), ⟨div_pos (by linarith [hx.1]) (mul_pos two_pos hr),
      (div_lt_one (mul_pos two_pos hr)).mpr (by linarith [hx.2])⟩, ?_⟩
    change (line ⟨-r, -r * s⟩ ⟨r, r * s⟩).eval 0 _ = _
    simp only [eval_line, hkeep rfl, zero_mul, add_zero, AffineMap.lineMap_apply_module,
      Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul]
    constructor <;> field_simp [hr.ne'] <;> ring

private theorem member_first_vector (r s d : ℝ) (keep : Bool)
    (hkeep : keep = true → d = 0) :
    (member r s d keep).germ false =
      (if keep then (2 : ℝ) else 1) • (⟨r, r * s + d⟩ : ℂ) := by
  cases keep <;> apply Complex.ext <;>
    simp [member, slopeDetour, germ_append, germ_line, hkeep, Complex.real_smul, two_mul, add_comm]

private theorem contact_abscissa {r s t d e q x y : ℝ} (hr : 0 < r) (hst : s ≠ t)
    (hq : 0 < q) (hd : d - e = (s - t) * q) (hx : x ∈ Set.Icc (-r) r)
    (hs : y = s * x + d * (1 - |x| / r))
    (ht : y = t * x + e * (1 - |x| / r)) : x = -r * q / (r + q) := by
  have hprod : (s - t) * (x + q * (1 - |x| / r)) = 0 := by
    calc
      _ = (s - t) * x + (d - e) * (1 - |x| / r) := by rw [hd]; ring
      _ = 0 := by linarith
  have hzero := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hst)
  have hneg : x < 0 := lt_of_not_ge fun hnonneg => by
    rw [abs_of_nonneg hnonneg] at hzero
    have hw : 0 ≤ 1 - x / r := sub_nonneg.mpr ((div_le_one hr).mpr hx.2)
    obtain rfl : x = 0 := by linarith only [hzero, hnonneg, mul_nonneg hq.le hw]
    simp [hq.ne'] at hzero
  rw [abs_of_neg hneg] at hzero
  apply (eq_div_iff (by linarith only [hr, hq] : r + q ≠ 0)).mpr
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
  have hx : -r / 3 < x ∧ x < 0 :=
    ⟨(lt_div_iff₀ hrq).mpr (by nlinarith only [hr, hqr]),
      div_neg_of_neg_of_pos (by nlinarith only [hr, hq]) hrq⟩
  have hxr : x ∈ Set.Ioo (-r) 0 := ⟨by linarith only [hr, hx.1], hx.2⟩
  have hroot : s * x + d * (1 + x / r) = t * x + e * (1 + x / r) := by
    suffices (s - t) * x + (d - e) * (1 + x / r) = 0 by linarith
    rw [hd]
    dsimp only [x]
    field_simp [hr.ne', hrq.ne']; ring
  obtain ⟨u, hu, hue⟩ : ∃ u ∈ Set.Ioo (0 : ℝ) 1, (member r s d keep).eval 0 u = z :=
    member_first hr hk hxr
  obtain ⟨v, hv, hve⟩ := member_first (s := t) hr hk' hxr
  replace hve : (member r t e keep').eval 0 v = z := hve.trans (Complex.ext rfl hroot.symm)
  have hz : z ∈ (member r s d keep).support ∧ z ∈ (member r t e keep').support :=
    ⟨hue ▸ (member r s d keep).at_mem_support 0 ⟨hu.1.le, hu.2.le⟩,
     hve ▸ (member r t e keep').at_mem_support 0 ⟨hv.1.le, hv.2.le⟩⟩
  have common {w : ℂ} (hw : w ∈ (member r s d keep).support)
      (hw' : w ∈ (member r t e keep').support) : w = z := by
    obtain ⟨hwx, hwy⟩ := member_support hr hk hw
    obtain ⟨_, hwy'⟩ := member_support hr hk' hw'
    have hwre := contact_abscissa hr hst hq hd hwx hwy hwy'
    apply Complex.ext hwre
    rw [hwy, hwre, abs_of_neg hx.2]
    dsimp only [z]
    ring
  refine ⟨⟨z, hz, fun w hw => common hw.1 hw.2⟩,
    fun w hw hw' => common hw hw' ▸ ⟨hx.1, hx.2, u, v, hu, hv, hue, hve⟩, ?_⟩
  · rw [member_first_vector r s d keep hk, member_first_vector r t e keep' hk']
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    have hm (b : Bool) : (if b then (2 : ℝ) else 1) ≠ 0 := by cases b <;> norm_num
    rw [show ∀ m n : ℝ, m * r * (n * (r * t + e)) - m * (r * s + d) * (n * r) =
      m * n * r * (t - s) * (r + q) from fun m n => by linear_combination -(m * n * r) * hd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hm _) (hm _)) hr.ne')
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
  exact Complex.ext rfl (by dsimp [lift, parabolaPoint, height]; ring)

private theorem lift_injective {a c μ : ℝ} (hμ : μ ≠ 0) :
    Function.Injective (lift a c μ) := by
  intro z w h
  have hre : z.re = w.re := (congrArg Complex.re h :)
  exact Complex.ext hre (by simpa [lift, hre, hμ] using congrArg Complex.im h)

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
    dsimp only [v]
    field_simp [hus.ne']; ring
  have hd : (1 - v) * height a c μ s + v * height a c μ u = height a c μ t := by
    refine mul_left_cancel₀ hw ?_
    linear_combination ht - (1 - v) * hs - v * hu - x * hinterp
  have hpoint : AffineMap.lineMap (parabolaPoint s) (parabolaPoint u) v = parabolaPoint t :=
    lift_injective hμ <| by
      rw [AffineMap.apply_lineMap, lift_parabola, lift_parabola, lift_parabola]
      exact Complex.ext (by simpa [AffineMap.lineMap_apply_module] using hinterp)
        (by simpa [AffineMap.lineMap_apply_module] using hd)
  have hmem := hpoint ▸ lineMap_mem_segment ℝ (parabolaPoint s) (parabolaPoint u) hv
  exact ((parabolaPoint_mem_segment_iff s u t).mp hmem).elim hst.ne' htu.ne

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
  obtain ⟨μ, hμ, hμlt⟩ := exists_between
    (by positivity : 0 < min (ε / (B + 1)) (r / (2 * (Q + 1))))
  obtain ⟨hμε, hμr⟩ := lt_min_iff.mp hμlt
  replace hμε : μ * (B + 1) < ε := (lt_div_iff₀ (by positivity)).mp hμε
  replace hμr : μ * (2 * (Q + 1)) < r := (lt_div_iff₀ (by positivity)).mp hμr
  let d := fun i => height a c μ (s i)
  let keep := fun i => decide (fixedIndex = some i)
  let R := fun i => member r (s i) (d i) (keep i)
  have hM_i (i : ι) : |s i - a| ≤ M :=
    Finset.single_le_sum (fun j _ => abs_nonneg (s j - a)) (Finset.mem_univ i)
  have hd (i : ι) : |d i| < ε := by
    obtain ⟨h1, h2⟩ := abs_le.mp (hM_i i)
    have hle : |(s i - a) ^ 2 + c * (s i - a)| ≤ M ^ 2 + c * M :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    calc
      |d i| = μ * |(s i - a) ^ 2 + c * (s i - a)| := by
        simp only [d, height, abs_mul, abs_of_pos hμ]
      _ ≤ μ * B := mul_le_mul_of_nonneg_left hle hμ.le
      _ < ε := by linarith only [hμ, hμε]
  have hkeep (i : ι) (hi : keep i = true) : d i = 0 := by
    simp [d, height, a, of_decide_eq_true hi]
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
    have hfactor : 1 ≤ s i + s j - 2 * a + c ∧ s i + s j - 2 * a + c ≤ Q := by
      dsimp only [c, Q]; constructor <;> linarith only [hi.1, hi.2, hj.1, hj.2]
    have hq : 0 < q := mul_pos hμ (by linarith only [hfactor.1])
    have hqr : q < r / 2 := by linarith only [hμ, hμr, mul_le_mul_of_nonneg_left hfactor.2 hμ.le]
    exact pair_separation hr (fun h => hij (hs h)) hq hqr
      (height_sub a c μ (s i) (s j)) (keep i) (keep j) (hkeep i) (hkeep j)
  refine ⟨d, ?_⟩
  have hR : (fun i =>
      if fixedIndex = some i then line ⟨-r, -r * s i⟩ ⟨r, r * s i⟩
      else slopeDetour r (s i) (d i)) = R := funext fun i => by simp [R, member, keep]
  rw [hR]
  refine ⟨fun i => ⟨(member_ends r (s i) (d i) (keep i)).1,
      (member_ends r (s i) (d i) (keep i)).2, member_simple hr _ _ _,
      fun _ hz => member_tube hr (hkeep i) (hd i) hz⟩,
    fun f hf => ⟨by simp [d, height, a, hf], by simp [R, member, keep, hf]⟩,
    fun i j hij => (hpair i j hij).1, fun i j hij => (hpair i j hij).2.1,
    fun i j hij => (hpair i j hij).2.2, ?_⟩
  · intro i j k hij hik hjk z hi hj hk
    obtain ⟨hx, hz0, _⟩ := (hpair i j hij).2.1 z hi hj
    have hw : 0 < 1 - |z.re| / r := by
      rw [abs_of_neg hz0, sub_pos, div_lt_one hr]; linarith
    have hsupp {m} (hm : z ∈ (R m).support) :
        z.im = s m * z.re + (1 - |z.re| / r) * height a c μ (s m) := by
      simpa only [d, mul_comm (height a c μ (s m))] using (member_support hr (hkeep m) hm).2
    exact no_three hμ.ne' hw.ne' (mt (@hs _ _) hij) (mt (@hs _ _) hik) (mt (@hs _ _) hjk)
      (hsupp hi) (hsupp hj) (hsupp hk)

end Cslib.Polygonal
