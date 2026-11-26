/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.CrossingNeighborhoods
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.FrozenReference
public import CslibFrontier.Foundations.Geometry.Polygonal.Reverse
public import CslibFrontier.Foundations.Geometry.Polygonal.Translation
public import CslibFrontier.Foundations.Geometry.Polygonal.SlopeDetour
import CslibFrontier.Foundations.Geometry.Polygonal.RouteInterior
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local source-oriented detours at actual reference crossings

One actual crossing determines its finite family of incident indexed routes. Slopes and
an optional frozen member are derived internally. Horizontal cut margins and finite slope
bounds choose local detours inside any given positive-radius ball, with the original source
orientation and literal one-segment protected cuts. All parameters and contacts are actual
polygonal route parameters; reversing a free member moves its old first piece to its last.

## Main results

* `Cslib.Complexity.Graph.RotationRecognition.exists_reference_detour_placement`: actual
  simple local routes, source cut endpoints, protected line identity, unique transverse
  pair contacts and no triple contact inside a given ball.

These are local cuts. `exists_reference_patch_assembly` assembles them into simple global
routes while retaining frozen routes literally. The downstream
`exists_reference_crossing_regularization` in `ReferenceRegularization` proves exact
pair-contact correspondence, transverse contacts and no triples away from declared vertices.
Parity, frozen placement, Hanani–Tutte and query/source recognition remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Polygonal

private def placed (p : Route) (flip : Bool) (z : ℂ) : Route :=
  (if flip then p.reverse else p).translate z

private def contactIndex (p : Route) (flip : Bool) (z : ℂ) :
    Fin (placed p flip z).segments := by
  cases flip
  · exact 0
  · exact (0 : Fin p.segments).rev

private def contactTime (flip : Bool) (t : ℝ) : ℝ := if flip then 1 - t else t

private theorem placed_support (p : Route) (flip : Bool) (z : ℂ) :
    (placed p flip z).support = (fun w => z + w) '' p.support := by
  cases flip <;> simp only [placed, Bool.false_eq_true, ↓reduceIte,
    Route.support_translate, Route.support_reverse]

private theorem mem_placed_support {p : Route} {flip : Bool} {z w : ℂ} :
    w ∈ (placed p flip z).support ↔ w - z ∈ p.support := by
  rw [placed_support]
  exact ⟨fun ⟨u, hu, h⟩ => by rwa [← h, add_sub_cancel_left],
    fun h => ⟨w - z, h, add_sub_cancel _ _⟩⟩

private theorem placed_simple {p : Route} (hp : p.IsSimple) (flip : Bool) (z : ℂ) :
    (placed p flip z).IsSimple :=
  flip.rec (hp.translate z) (hp.reverse.translate z)

private theorem placed_contact_eval (p : Route) (flip : Bool) (z : ℂ) (t : ℝ) :
    (placed p flip z).eval (contactIndex p flip z) (contactTime flip t) = z + p.eval 0 t := by
  cases flip
  · exact Route.eval_translate p z 0 t
  · change (p.reverse.translate z).eval (0 : Fin p.segments).rev (1 - t) = _
    have hi : ((0 : Fin p.segments).rev : Fin p.reverse.segments).rev = 0 := Fin.rev_rev _
    exact (Route.eval_translate _ z _ _).trans
      (congrArg (fun w => z + w) ((Route.eval_reverse p _ _).trans
        (congrArg₂ (fun (i : Fin p.segments) (u : ℝ) => p.eval i u) hi
          (sub_sub_cancel 1 t))))

private theorem placed_vector (p : Route) (flip : Bool) (z : ℂ) :
    let i := contactIndex p flip z
    (placed p flip z).point i.succ - (placed p flip z).point i.castSucc =
      if flip then -p.germ false else p.germ false := by
  dsimp only
  have h0 := placed_contact_eval p flip z 0
  have h1 := placed_contact_eval p flip z 1
  have hvec (q : Route) (i : Fin q.segments) :
      q.point i.succ - q.point i.castSucc = q.eval i 1 - q.eval i 0 := by
    simp only [Route.eval, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]
  rw [hvec]
  cases flip <;> simp only [contactTime, Bool.false_eq_true, ↓reduceIte, sub_zero,
    sub_self] at h0 h1 ⊢ <;> rw [h0, h1] <;>
    simp only [Route.eval, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
      add_sub_add_left_eq_sub, Fin.castSucc_zero, Route.germ,
      Bool.false_eq_true, ↓reduceIte, Route.start, neg_sub]

private theorem cut_parameters {a b : ℝ} (hab : a ≠ b) {z : ℂ}
    (hz : z ∈ openSegment ℝ (parabolaPoint a) (parabolaPoint b)) {r : ℝ} (hr : 0 < r)
    (hm : r < min (z.re - min a b) (max a b - z.re)) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ β < 1 ∧
      AffineMap.lineMap (parabolaPoint a) (parabolaPoint b) α =
        z + (if b < a then (⟨r, r * (a + b)⟩ : ℂ) else ⟨-r, -r * (a + b)⟩) ∧
      AffineMap.lineMap (parabolaPoint a) (parabolaPoint b) β =
        z + (if b < a then (⟨-r, -r * (a + b)⟩ : ℂ) else ⟨r, r * (a + b)⟩) := by
  obtain ⟨hbetween, hline⟩ := (mem_openChord_iff hab z).mp hz
  have hshift (x : ℝ) (hx : |x| < min (z.re - min a b) (max a b - z.re)) :
      z + (⟨x, x * (a + b)⟩ : ℂ) ∈ openSegment ℝ (parabolaPoint a) (parabolaPoint b) := by
    have hx' := lt_min_iff.mp hx
    simp only [mem_openChord_iff hab, Set.mem_Ioo, Complex.add_re, Complex.add_im]
    exact ⟨⟨by linarith [neg_abs_le x, hbetween.1],
      by linarith [le_abs_self x, hbetween.2]⟩,
      by nlinarith only [hline]⟩
  have hleft := hshift (-r) (by simpa only [abs_neg, abs_of_pos hr] using hm)
  have hright := hshift r (by simpa only [abs_of_pos hr] using hm)
  rw [openSegment_eq_image_lineMap] at hleft hright
  obtain ⟨l, hl, hleq⟩ := hleft
  obtain ⟨u, hu, hueq⟩ := hright
  have hxl : (1 - l) * a + l * b = z.re - r := by
    simpa [AffineMap.lineMap_apply_module, Complex.real_smul, parabolaPoint, sub_eq_add_neg] using
      congrArg Complex.re hleq
  have hxu : (1 - u) * a + u * b = z.re + r := by
    simpa [AffineMap.lineMap_apply_module, Complex.real_smul, parabolaPoint, sub_eq_add_neg] using
      congrArg Complex.re hueq
  rcases lt_or_gt_of_ne hab with hab' | hba
  · have hlu : l < u := by
      by_contra h
      have hmul : 0 ≤ (l - u) * (b - a) :=
        mul_nonneg (sub_nonneg.mpr (not_lt.mp h)) (sub_nonneg.mpr hab'.le)
      nlinarith only [hmul, hxl, hxu, hr]
    exact ⟨l, u, hl.1, hlu, hu.2, by simpa only [ite_eq_right (not_lt.mpr hab'.le)] using hleq,
      by simpa only [ite_eq_right (not_lt.mpr hab'.le)] using hueq⟩
  · have hul : u < l := by
      by_contra h
      have hmul : 0 ≤ (u - l) * (a - b) :=
        mul_nonneg (sub_nonneg.mpr (not_lt.mp h)) (sub_nonneg.mpr hba.le)
      nlinarith only [hmul, hxl, hxu, hr]
    exact ⟨u, l, hu.1, hul, hl.2, by simpa only [ite_eq_left hba] using hueq,
      by simpa only [ite_eq_left hba] using hleq⟩

private theorem choose_geometry {ι : Type*} [Finite ι] (s m : ι → ℝ)
    (hm : ∀ i, 0 < m i) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ (∀ i, r < m i) ∧
      (∀ i, r * (1 + |s i|) + ε < ρ) := by
  classical
  let := Fintype.ofFinite ι
  let K := 1 + ∑ i, |s i|
  let T := 1 + ∑ i, 1 / m i
  let r := min (ρ / (4 * K)) (1 / (2 * T))
  let ε := ρ / 4
  have hsumK : 0 ≤ ∑ i, |s i| := Finset.sum_nonneg fun i _ => abs_nonneg (s i)
  have hsumT : 0 ≤ ∑ i, 1 / m i :=
    Finset.sum_nonneg fun i _ => (div_pos zero_lt_one (hm i)).le
  have hK : 0 < K := by dsimp [K]; linarith
  have hT : 0 < T := by dsimp [T]; linarith
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, ε, hr, by dsimp [ε]; positivity, ?_, ?_⟩
  · intro i
    have hTi : 1 / m i < T := by
      dsimp [T]
      linarith [Finset.single_le_sum (fun j _ => (div_pos zero_lt_one (hm j)).le)
        (Finset.mem_univ i)]
    have hprod := (div_lt_iff₀ (hm i)).mp hTi
    exact (min_le_right _ _).trans_lt ((div_lt_iff₀ (by positivity)).mpr (by nlinarith))
  · intro i
    have hKi : 1 + |s i| ≤ K := by
      dsimp [K]
      linarith [Finset.single_le_sum (fun j _ => abs_nonneg (s j)) (Finset.mem_univ i)]
    have hK0 : 0 < 4 * K := by positivity
    have hrK := (le_div_iff₀ hK0).mp (min_le_left _ _ : r ≤ _)
    dsimp [ε]; nlinarith [mul_le_mul_of_nonneg_left hKi hr.le]

/-- Place the actual finite incident family inside any positive-radius ball. Source cut
parameters, optional frozen protection, slopes and all geometric conclusions are internal.
The protected local route is literally a single cut line; no global route is constructed. -/
theorem exists_reference_detour_placement {I : FixedRotationInput} (hI : Valid I) {z : ℂ}
    (hz : ∃ e f : Fin (subdivisionGraph I).edges.length, e ≠ f ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route e).start
        ((referenceDrawing I).route e).finish ∧
      z ∈ openSegment ℝ ((referenceDrawing I).route f).start
        ((referenceDrawing I).route f).finish) {ρ : ℝ} (hρ : 0 < ρ) :
    let D := referenceDrawing I
    let E := Fin (subdivisionGraph I).edges.length
    let F : E → Bool := fun e => ((subdivide I)[e.val]'(by
      simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen
    let X := {e : E // z ∈ (D.route e).support}
    let s : X → ℝ := fun e => (D.route e.val).start.re + (D.route e.val).finish.re
    ∃ r : ℝ, 0 < r ∧ ∃ d α β : X → ℝ,
      let R : X → Route := fun e => if F e.val then
        Route.line ⟨-r, -r * s e⟩ ⟨r, r * s e⟩ else Route.slopeDetour r (s e) (d e)
      let P : X → Route := fun e =>
        (if decide ((D.route e.val).finish.re < (D.route e.val).start.re)
          then (R e).reverse else R e).translate z
      (∀ e, 0 < α e ∧ α e < β e ∧ β e < 1 ∧
        (P e).start = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α e) ∧
        (P e).finish = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β e) ∧
        (P e).IsSimple ∧ (P e).support ⊆ Metric.ball z ρ) ∧
      (∀ e, F e.val = true → d e = 0 ∧
        P e = Route.line (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α e))
          (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β e))) ∧
      (∀ e f, e ≠ f → ∃! w : ℂ, w ∈ (P e).support ∧ w ∈ (P f).support) ∧
      (∀ e f, e ≠ f → ∀ w : ℂ, w ∈ (P e).support → w ∈ (P f).support →
        ∃ (i : Fin (P e).segments) (j : Fin (P f).segments) (u v : ℝ),
          u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧ (P e).eval i u = w ∧ (P f).eval j v = w ∧
          let a := (P e).point i.succ - (P e).point i.castSucc
          let b := (P f).point j.succ - (P f).point j.castSucc
          a.re * b.im - a.im * b.re ≠ 0) ∧
      (∀ e f g, e ≠ f → e ≠ g → f ≠ g → ∀ w : ℂ,
        w ∈ (P e).support → w ∈ (P f).support → w ∉ (P g).support) := by
  classical
  let D := referenceDrawing I
  let E := Fin (subdivisionGraph I).edges.length
  let F : E → Bool := fun e => ((subdivide I)[e.val]'(by
    simpa only [subdivisionGraph, List.length_map] using e.isLt)).frozen
  let X := {e : E // z ∈ (D.route e).support}
  let : DecidableEq X := fun e f => Classical.propDecidable (e = f)
  let a : E → ℝ := fun e => (D.route e).start.re
  let b : E → ℝ := fun e => (D.route e).finish.re
  have hne (e : E) : a e ≠ b e := fun hab =>
    (Route.isSimple_line_iff _ _).mp (referenceDrawing_simple hI e) (congrArg parabolaPoint hab)
  have hopen (e : X) : z ∈ openSegment ℝ (D.route e.val).start (D.route e.val).finish := by
    have hend (tag : Bool) : z ≠ (D.route e.val).endpoint tag := by
      rw [D.endpoint_eq]
      apply referenceDrawing_crossing_ne_vertex hI hz
      exact ((referenceOrder_enumerates hI).2 _).mp ((subdivision_endpoint_spec hI e.val).1 tag)
    apply mem_openSegment_of_ne_left_right (hend false).symm (hend true).symm
    exact (Route.support_line _ _) ▸ e.property
  let s : X → ℝ := fun e => a e.val + b e.val
  have hs : Function.Injective s := fun e f heq => Subtype.ext <| by_contra fun hef =>
    referenceDrawing_slope_ne_of_interior_contact hI e.val f.val hef (hopen e) (hopen f) heq
  have hF : ∀ e f : X, F e.val = true → F f.val = true → e = f := by
    intro e f he hf
    by_contra hef
    have hef' : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    simp only [openSegment_eq_image_lineMap] at hopen
    obtain ⟨u, hu, hueq⟩ := hopen e
    obtain ⟨v, hv, hveq⟩ := hopen f
    obtain ⟨be, _, hbe, _, _⟩ := referenceDrawing_frozen_edge_contacts hI e.val f.val
      hef' he hf 0 0 ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩
      (((Route.eval_line _ _ 0 u).trans hueq).trans ((Route.eval_line _ _ 0 v).trans hveq).symm)
    exact (Route.not_atEnd_of_mem_Ioo _ 0 hu be) hbe
  let fixed : Option X := if h : ∃ e : X, F e.val = true then some h.choose else none
  have hfixed (e : X) : fixed = some e ↔ F e.val = true := by
    dsimp only [fixed]
    split_ifs with h
    · exact ⟨fun he => Option.some.inj he ▸ h.choose_spec,
        fun he => congrArg some (hF h.choose e h.choose_spec he)⟩
    · exact ⟨fun he => he.elim, fun he => (h ⟨e, he⟩).elim⟩
  let m : X → ℝ := fun e => min (z.re - min (a e.val) (b e.val))
    (max (a e.val) (b e.val) - z.re)
  have hm (e : X) : 0 < m e := by
    obtain ⟨hx, _⟩ := (mem_openChord_iff (hne e.val) z).mp (hopen e)
    exact lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  obtain ⟨r, ε, hr, hε, hrm, htube⟩ := choose_geometry s m hm hρ
  have hcut (e : X) := cut_parameters (hne e.val) (hopen e) hr (hrm e)
  choose α β hα hαβ hβ hcutA hcutB using hcut
  obtain ⟨d, hsep⟩ := exists_slopeDetour_separation s hs hr hε fixed
  dsimp only at hsep
  simp_rw [hfixed] at hsep
  obtain ⟨hends, hkeep, hpair, hcontact, hdet, hno3⟩ := hsep
  let R : X → Route := fun e => if F e.val then
    Route.line ⟨-r, -r * s e⟩ ⟨r, r * s e⟩ else Route.slopeDetour r (s e) (d e)
  have hraw (e : X) :
      (if fixed = some e then Route.line ⟨-r, -r * s e⟩ ⟨r, r * s e⟩
        else Route.slopeDetour r (s e) (d e)) = R e := by
    simp only [hfixed, R]
  have hraw_eval (e : X) (t : ℝ) := congrArg (fun q : Route => q.eval 0 t) (hraw e)
  let flip : X → Bool := fun e => decide (b e.val < a e.val)
  let P : X → Route := fun e => placed (R e) (flip e) z
  have hEndR (e : X) (tag : Bool) : (R e).endpoint tag =
      if tag then (⟨r, r * s e⟩ : ℂ) else ⟨-r, -r * s e⟩ :=
    tag.rec (hends e).1 (hends e).2.1
  have htransport (e : X) (tag : Bool) :
      (P e).endpoint tag = z + (R e).endpoint (if flip e then !tag else tag) := by
    change ((if flip e then (R e).reverse else R e).translate z).endpoint tag = _
    rw [Route.endpoint_translate]
    cases flip e <;> simp only [Bool.false_eq_true, ↓reduceIte, Route.endpoint_reverse]
  have hpoint (e : X) (tag : Bool) : (P e).endpoint tag =
      AffineMap.lineMap (D.route e.val).start (D.route e.val).finish
        (if tag then β e else α e) := by
    have hc : AffineMap.lineMap (D.route e.val).start (D.route e.val).finish
        (if tag then β e else α e) = z +
        (if tag then (if b e.val < a e.val then (⟨-r, -r * s e⟩ : ℂ) else ⟨r, r * s e⟩)
          else (if b e.val < a e.val then (⟨r, r * s e⟩ : ℂ) else ⟨-r, -r * s e⟩)) :=
      tag.rec (hcutA e) (hcutB e)
    rw [htransport, hEndR, hc]
    congr 1
    cases tag <;> by_cases hf : b e.val < a e.val <;>
      simp only [flip, hf, decide_true, decide_false, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
  have hpointA (e : X) :
      (P e).start = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α e) :=
    hpoint e false
  have hpointB (e : X) :
      (P e).finish = AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β e) :=
    hpoint e true
  have hball (e : X) : (P e).support ⊆ Metric.ball z ρ := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := (placed_support (R e) (flip e) z) ▸ hw
    obtain ⟨hx, hy⟩ := (hends e).2.2.2 v hv
    have hxab : |v.re| ≤ r := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hyab : |v.im| ≤ |v.im - s e * v.re| + |s e| * r := by
      calc
        |v.im| = |(v.im - s e * v.re) + s e * v.re| := by congr 1; ring
        _ ≤ |v.im - s e * v.re| + |s e * v.re| := abs_add_le _ _
        _ ≤ |v.im - s e * v.re| + |s e| * r := by
          rw [abs_mul]
          exact add_le_add_right (mul_le_mul_of_nonneg_left hxab (abs_nonneg _)) _
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    nlinarith [Complex.norm_le_abs_re_add_abs_im v, htube e]
  have hPkeep (e : X) (he : F e.val = true) : d e = 0 ∧
      P e = Route.line (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (α e))
        (AffineMap.lineMap (D.route e.val).start (D.route e.val).finish (β e)) := by
    refine ⟨(hkeep e he).1, ?_⟩
    rw [← hpointA e, ← hpointB e]
    dsimp only [P, placed, R]
    cases flip e <;> simp [he, Route.reverse_line, Route.translate_line]
  refine ⟨r, hr, d, α, β, ?_, hPkeep, ?_, ?_, ?_⟩
  · exact fun e => ⟨hα e, hαβ e, hβ e, hpointA e, hpointB e,
      placed_simple (hends e).2.2.1 (flip e) z, hball e⟩
  · intro e f hef
    obtain ⟨w, ⟨he, hf⟩, huniq⟩ := hpair e f hef
    refine ⟨z + w, ⟨mem_placed_support.mpr (by simpa using he),
      mem_placed_support.mpr (by simpa using hf)⟩, fun v hv => ?_⟩
    rw [← add_sub_cancel z v,
      huniq (v - z) ⟨mem_placed_support.mp hv.1, mem_placed_support.mp hv.2⟩]
  · intro e f hef w hwe hwf
    obtain ⟨_, _, t, t', ht, ht', hete, hetf⟩ :=
      hcontact e f hef (w - z) (mem_placed_support.mp hwe) (mem_placed_support.mp hwf)
    refine ⟨contactIndex (R e) (flip e) z, contactIndex (R f) (flip f) z,
      contactTime (flip e) t, contactTime (flip f) t', ?_, ?_, ?_, ?_, ?_⟩
    · cases flip e <;> dsimp [contactTime] <;> constructor <;> linarith [ht.1, ht.2]
    · cases flip f <;> dsimp [contactTime] <;> constructor <;> linarith [ht'.1, ht'.2]
    · exact (placed_contact_eval (R e) (flip e) z t).trans
        (by rw [← hraw_eval, hete, add_sub_cancel])
    · exact (placed_contact_eval (R f) (flip f) z t').trans
        (by rw [← hraw_eval, hetf, add_sub_cancel])
    · have hve := placed_vector (R e) (flip e) z
      have hvf := placed_vector (R f) (flip f) z
      dsimp only [placed, flip, a, b, D] at hve hvf ⊢
      rw [hve, hvf]
      have hd := hdet e f hef
      change ((R e).germ false).re * ((R f).germ false).im -
        ((R e).germ false).im * ((R f).germ false).re ≠ 0 at hd
      split_ifs <;> intro hzero <;> apply hd
      all_goals
        try simp only [Complex.neg_re, Complex.neg_im] at hzero
        nlinarith only [hzero]
  · intro e f g hef heg hfg w hwe hwf hwg
    exact hno3 e f g hef heg hfg (w - z) (mem_placed_support.mp hwe)
      (mem_placed_support.mp hwf) (mem_placed_support.mp hwg)

end Cslib.Complexity.Graph.RotationRecognition
