/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.HorizontalTransport
public import CslibFrontier.Foundations.Geometry.Polygonal.ComplexMul
import CslibFrontier.Foundations.Geometry.FiniteLineAvoidance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transport of one declared vertex to an unoccupied target

`IsEmbedding.exists_single_vertex_transport` constructs two actual conjugated plateau
shears. All directions, the intermediate point and widths are internal. It preserves
embedding, the exact declared-name update, positive ORIGINAL end-germ factors and clockwise
order, with at most25 times each original route's segment count. An unchanged target uses
literally the original drawing. Nonincident routes may change; undeclared names are not
subject to a Function.update identity.

This original finite PL component does not position all vertices or straighten a frozen
forest. Finite parking, frozen literal placement, moves/parity, HT and the full query/source
recognition criterion remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

private def chart {G : Graph} (u : ℂ) (D : PolygonalDrawing G) : PolygonalDrawing G where
  vertex := fun w => u * D.vertex w
  route := fun e => Route.mulComplex u (D.route e)
  endpoint_eq := fun e b => by rw [Route.endpoint_mulComplex, D.endpoint_eq]

private theorem chart_germ {G : Graph} (u : ℂ) (D : PolygonalDrawing G) (a : Dart G) :
    (chart u D).germ a = u * D.germ a := Route.germ_mulComplex u (D.route a.1) a.2

private theorem chart_embedding {G : Graph} {D : PolygonalDrawing G} (hD : D.IsEmbedding)
    {u : ℂ} (hu : u ≠ 0) : (chart u D).IsEmbedding := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb he
    exact hD.vertices_injective ha hb (mul_left_cancel₀ hu he)
  · intro e
    exact (hD.simple e).mulComplex hu
  · intro e i t ht v hv he
    change Fin (D.route e).segments at i
    have heq : u * (D.route e).eval i t = u * D.vertex v :=
      (Route.eval_mulComplex u (D.route e) i t).symm.trans he
    exact hD.vertex_contacts e i t ht v hv (mul_left_cancel₀ hu heq)
  · intro e f hef i j s t hs ht he
    change Fin (D.route e).segments at i
    change Fin (D.route f).segments at j
    have heq := (Route.eval_mulComplex u (D.route e) i s).symm.trans
      (he.trans (Route.eval_mulComplex u (D.route f) j t))
    exact hD.edge_contacts e f hef i j s t hs ht (mul_left_cancel₀ hu heq)

-- Off-line witnesses are ALL-real. The only scalar inverse characterization here is the
-- offered Complex.inv_im formula; no parallel public collinearity notion is introduced.
private theorem off_line_inv_im_ne {a p z : ℂ} (hpa : p ≠ a)
    (hline : ∀ t : ℝ, AffineMap.lineMap a p t ≠ z) :
    (((z - a) / (p - a))⁻¹).im ≠ 0 := by
  let R := (z - a) / (p - a)
  have him : R.im ≠ 0 := by
    intro he
    have hreal : (R.re : ℂ) = R := by
      simpa only [he, Complex.ofReal_zero, zero_mul, add_zero] using Complex.re_add_im R
    apply hline R.re
    rw [AffineMap.lineMap_apply_module', Complex.real_smul, hreal]
    change (z - a) / (p - a) * (p - a) + a = z
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hpa), sub_add_cancel]
  have hR : R ≠ 0 := fun he => him (by rw [he]; rfl)
  rw [Complex.inv_im]
  exact div_ne_zero (neg_ne_zero.mpr him) (fun he => hR (Complex.normSq_eq_zero.mp he))

private theorem first_height {a p z : ℂ} (hpa : p ≠ a) (hza : z ≠ a)
    (hline : ∀ t : ℝ, AffineMap.lineMap a p t ≠ z) :
    (((z - a)⁻¹) * p).im ≠ (((z - a)⁻¹) * a).im := by
  have hn := off_line_inv_im_ne hpa hline
  intro he
  apply hn
  have hid : ((z - a) / (p - a))⁻¹ = (z - a)⁻¹ * (p - a) := by
    field_simp [sub_ne_zero.mpr hpa, sub_ne_zero.mpr hza]
  rw [hid, mul_sub, Complex.sub_im, he, sub_self]

private theorem second_height {q p z : ℂ} (hpq : p ≠ q) (hzq : z ≠ q)
    (hline : ∀ t : ℝ, AffineMap.lineMap q p t ≠ z) :
    (((q - z)⁻¹) * p).im ≠ (((q - z)⁻¹) * z).im := by
  have hn := off_line_inv_im_ne hpq hline
  intro he
  have hid : (q - z)⁻¹ * (p - z) = 1 - ((z - q) / (p - q))⁻¹ := by
    field_simp [sub_ne_zero.mpr hpq, sub_ne_zero.mpr hzq,
      sub_ne_zero.mpr hzq.symm]
    ring
  have hi := congrArg Complex.im hid
  rw [mul_sub, Complex.sub_im, he, sub_self, Complex.sub_im, Complex.one_im] at hi
  exact hn (by linarith)

private theorem transport_leg {G : Graph} {D : PolygonalDrawing G} (hD : D.IsEmbedding)
    (hG : G.incidenceVertices ⊆ G.vertices) (v : ℕ) (hv : v ∈ G.vertices) (b : ℂ)
    (hmove : b ≠ D.vertex v)
    (hheight : ∀ w ∈ G.vertices, w ≠ v →
      (((b - D.vertex v)⁻¹) * D.vertex w).im ≠
        (((b - D.vertex v)⁻¹) * D.vertex v).im) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧
      (∀ w ∈ G.vertices, E.vertex w = if w = v then b else D.vertex w) ∧
      (∀ a : Dart G, ∃ c : ℝ, 0 < c ∧ E.germ a = c • D.germ a) ∧
      (∀ e, (E.route e).segments ≤ 5 * (D.route e).segments) := by
  let u := (b - D.vertex v)⁻¹
  have hu : u ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hmove)
  have hc : (chart u D).IsEmbedding := chart_embedding hD hu
  obtain ⟨r, hr, hall⟩ := hc.exists_horizontal_vertex_transport hG v hv hheight
  let F := (chart u D).plateauShear ((chart u D).vertex v).im r 1
  obtain ⟨hF, hpoints, hgerms, _, hcount, _⟩ := hall 1
  let E := chart u⁻¹ F
  refine ⟨E, chart_embedding hF (inv_ne_zero hu), ?_, ?_, ?_⟩
  · intro w hw
    change u⁻¹ * F.vertex w = _
    rw [hpoints w hw]
    by_cases he : w = v
    · subst w
      simp only [ite_true]
      change u⁻¹ * (u * D.vertex v + 1) = b
      calc
        _ = D.vertex v + u⁻¹ := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hu, one_mul, mul_one]
        _ = b := by dsimp only [u]; rw [inv_inv]; ring
    · simp only [ite_eq_right he]
      change u⁻¹ * (u * D.vertex w) = D.vertex w
      rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  · intro a
    obtain ⟨c, hc, hg⟩ := hgerms a
    refine ⟨c, hc, ?_⟩
    rw [chart_germ, hg, chart_germ]
    simp only [Complex.real_smul]
    calc
      u⁻¹ * ((c : ℂ) * (u * D.germ a)) = (c : ℂ) * ((u⁻¹ * u) * D.germ a) := by ring
      _ = (c : ℂ) * D.germ a := by rw [inv_mul_cancel₀ hu, one_mul]
  · intro e
    exact hcount e

/-- Move one declared vertex to any target unoccupied by OTHER declared vertices. Two
internally chosen conjugated plateau shears preserve the actual embedding and ORIGINAL germ
rays, including both ends of loops. At most25 pieces per original segment suffice. Only
DECLARED names obey the update; nonincident and frozen routes are not claimed literal. -/
theorem IsEmbedding.exists_single_vertex_transport {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : G.incidenceVertices ⊆ G.vertices)
    (v : ℕ) (hv : v ∈ G.vertices) (q : ℂ)
    (hq : ∀ w ∈ G.vertices, w ≠ v → q ≠ D.vertex w) :
    ∃ D' : PolygonalDrawing G, D'.IsEmbedding ∧
      (∀ w ∈ G.vertices, D'.vertex w = if w = v then q else D.vertex w) ∧
      (∀ a : Dart G, ∃ c : ℝ, 0 < c ∧ D'.germ a = c • D.germ a) ∧
      (∀ x y z : Dart G, x.vertex = y.vertex → y.vertex = z.vertex →
        x ≠ y → y ≠ z → x ≠ z →
        (sbtw (D'.direction z) (D'.direction y) (D'.direction x) ↔
          sbtw (D.direction z) (D.direction y) (D.direction x))) ∧
      (∀ e, (D'.route e).segments ≤ 25 * (D.route e).segments) ∧
      (q = D.vertex v → D' = D) := by
  classical
  by_cases hsame : q = D.vertex v
  · refine ⟨D, hD, ?_, ?_, ?_, ?_, fun _ => rfl⟩
    · intro w _
      split_ifs with he
      · exact (congrArg D.vertex he).trans hsame.symm
      · rfl
    · intro a
      exact ⟨1, zero_lt_one, (one_smul ℝ _).symm⟩
    · intro x y z _ _ _ _ _
      rfl
    · intro e
      omega
  let P := G.vertices.toFinset.erase v
  let J := ({w : ℕ // w ∈ P} × Bool) ⊕ Unit
  let a : J → ℂ := Sum.elim (fun wb => if wb.2 then q else D.vertex v) (fun _ => D.vertex v)
  let b : J → ℂ := Sum.elim (fun wb => D.vertex wb.1.val) (fun _ => q)
  have hab : ∀ i : J, a i ≠ b i := by
    intro i
    rcases i with ⟨w, tag⟩ | _
    · have hw := Finset.mem_erase.mp w.property
      have hwdecl := List.mem_toFinset.mp hw.2
      cases tag
      · exact hD.vertex_ne hv hwdecl (Ne.symm hw.1)
      · exact hq w.val hwdecl hw.1
    · exact Ne.symm hsame
  obtain ⟨z, _, hlines⟩ := Cslib.exists_mem_ball_avoiding_lines a b hab (D.vertex v)
    (by norm_num : (0 : ℝ) < 1)
  have hxz : D.vertex v ≠ z := by
    simpa only [a, b, Sum.elim_inr, AffineMap.lineMap_apply_zero] using
      hlines (Sum.inr ()) 0
  have hqz : q ≠ z := by
    simpa only [a, b, Sum.elim_inr, AffineMap.lineMap_apply_one] using
      hlines (Sum.inr ()) 1
  have hfirst (w : ℕ) (hw : w ∈ G.vertices) (hwv : w ≠ v) (t : ℝ) :
      AffineMap.lineMap (D.vertex v) (D.vertex w) t ≠ z := by
    have hp : w ∈ P := Finset.mem_erase.mpr ⟨hwv, List.mem_toFinset.mpr hw⟩
    simpa only [a, b, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte] using
      hlines (Sum.inl (⟨w, hp⟩, false)) t
  have hsecond (w : ℕ) (hw : w ∈ G.vertices) (hwv : w ≠ v) (t : ℝ) :
      AffineMap.lineMap q (D.vertex w) t ≠ z := by
    have hp : w ∈ P := Finset.mem_erase.mpr ⟨hwv, List.mem_toFinset.mpr hw⟩
    simpa only [a, b, Sum.elim_inl, ↓reduceIte] using
      hlines (Sum.inl (⟨w, hp⟩, true)) t
  obtain ⟨D₁, hD₁, hpoint₁, hgerm₁, hcount₁⟩ := transport_leg hD hG v hv z hxz.symm
    (fun w hw hwv => first_height (hD.vertex_ne hw hv hwv) hxz.symm (hfirst w hw hwv))
  have hcenter : D₁.vertex v = z := by simpa only [ite_true] using hpoint₁ v hv
  have hother (w : ℕ) (hw : w ∈ G.vertices) (hwv : w ≠ v) : D₁.vertex w = D.vertex w := by
    simpa only [ite_eq_right hwv] using hpoint₁ w hw
  obtain ⟨D₂, hD₂, hpoint₂, hgerm₂, hcount₂⟩ := transport_leg hD₁ hG v hv q
    (by rw [hcenter]; exact hqz) (by
      intro w hw hwv
      rw [hcenter, hother w hw hwv]
      exact second_height (Ne.symm (hq w hw hwv)) hqz.symm (hsecond w hw hwv))
  have hg (x : Dart G) : ∃ c : ℝ, 0 < c ∧ D₂.germ x = c • D.germ x := by
    obtain ⟨c₁, hc₁, he₁⟩ := hgerm₁ x
    obtain ⟨c₂, hc₂, he₂⟩ := hgerm₂ x
    exact ⟨c₂ * c₁, mul_pos hc₂ hc₁, by rw [he₂, he₁, mul_smul]⟩
  have hdir (x : Dart G) : D₂.direction x = D.direction x := by
    obtain ⟨c, hc, he⟩ := hg x
    simp only [direction, he, Complex.real_smul, Complex.arg_real_mul _ hc]
  refine ⟨D₂, hD₂, ?_, hg, ?_, ?_, fun h => (hsame h).elim⟩
  · intro w hw
    rw [hpoint₂ w hw]
    split_ifs with he
    · rfl
    · exact hother w hw he
  · intro x y z _ _ _ _ _
    rw [hdir x, hdir y, hdir z]
  · intro e
    exact (hcount₂ e).trans (by nlinarith [hcount₁ e])

end Cslib.Complexity.Graph.PolygonalDrawing
