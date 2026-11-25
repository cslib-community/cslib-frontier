/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityColors

/-!
# Distinct endpoint rays of a segment arrangement

Nondegenerate segments that meet in at most one open point have distinct outgoing rays
at each common endpoint. The proof retains the indexed occurrences and both segment ends.
-/

public section

namespace Cslib.Polygonal

/-- Moving along either outgoing end vector is the actual affine segment parameter,
with the second end reversing the parameter. -/
theorem rayEndpoint_add_smul_endVector {ι : Type*} (a b : ι → ℂ)
    (e : ι × Bool) (t : ℝ) :
    rayEndpoint a b e + t • rayEndVector a b e =
      AffineMap.lineMap (a e.1) (b e.1) (if e.2 then 1 - t else t) := by
  rcases e with ⟨i, tag⟩
  cases tag <;> simp only [rayEndpoint, rayEndVector, Bool.false_eq_true, ↓reduceIte,
    AffineMap.lineMap_apply_module'] <;> module

/-- Nondegenerate segments have nonzero vectors at both indexed ends. -/
theorem rayEndVector_ne_zero {ι : Type*} (a b : ι → ℂ)
    (hab : ∀ i, a i ≠ b i) (e : ι × Bool) : rayEndVector a b e ≠ 0 := by
  rcases e with ⟨i, tag⟩
  cases tag <;> simp only [rayEndVector, Bool.false_eq_true, ↓reduceIte, sub_ne_zero]
  · exact (hab i).symm
  · exact hab i

/-- A segment arrangement with at most one open intersection per pair has distinct indexed
outgoing rays at each common endpoint. Equal rays would give two interior points in common. -/
theorem rayEndVector_injective_of_open_inter_subsingleton {ι : Type*}
    (a b : ι → ℂ) (hab : ∀ i, a i ≠ b i)
    (hinter : ∀ i j, i ≠ j →
      (openSegment ℝ (a i) (b i) ∩ openSegment ℝ (a j) (b j)).Subsingleton)
    (k e : ι × Bool) (hp : rayEndpoint a b e = rayEndpoint a b k)
    (harg : turnArg (rayEndVector a b e) = turnArg (rayEndVector a b k)) : e = k := by
  have harg' : (rayEndVector a b e).arg = (rayEndVector a b k).arg :=
    Complex.arg_coe_angle_eq_iff.mp (by
      simpa only [turnArg_coe_angle] using congrArg (fun t : ℝ => (t : Real.Angle)) harg)
  obtain ⟨s, hs, t, ht, hst⟩ := exists_small_smul_eq_of_arg_eq
    (rayEndVector_ne_zero a b hab e) (rayEndVector_ne_zero a b hab k) harg'
    (by norm_num : (0 : ℝ) < 1 / 3)
  have hparam (tag : Bool) {u : ℝ} (hu : u ∈ Set.Ioo 0 (1 / 3)) :
      (if tag then 1 - u else u) ∈ Set.Ioo (0 : ℝ) 1 := by
    cases tag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hu.1, hu.2]
  let pe : ℝ → ℂ := fun r => AffineMap.lineMap (a e.1) (b e.1) (if e.2 then 1 - r else r)
  let pk : ℝ → ℂ := fun r => AffineMap.lineMap (a k.1) (b k.1) (if k.2 then 1 - r else r)
  have hpoint {p q : ℝ} (hsame : p • rayEndVector a b e = q • rayEndVector a b k) :
      pe p = pk q := by
    dsimp only [pe, pk]
    rw [← rayEndpoint_add_smul_endVector, ← rayEndpoint_add_smul_endVector, hp, hsame]
  have hindex : e.1 = k.1 := by
    by_contra hne
    have hit {p q : ℝ} (hp' : p ∈ Set.Ioo 0 (1 / 3)) (hq : q ∈ Set.Ioo 0 (1 / 3))
        (hsame : p • rayEndVector a b e = q • rayEndVector a b k) :
        pe p ∈ openSegment ℝ (a e.1) (b e.1) ∩ openSegment ℝ (a k.1) (b k.1) :=
      ⟨lineMap_mem_openSegment ℝ _ _ (hparam e.2 hp'),
        hpoint hsame ▸ lineMap_mem_openSegment ℝ _ _ (hparam k.2 hq)⟩
    have hhalf : (s / 2) • rayEndVector a b e = (t / 2) • rayEndVector a b k := by
      simpa only [smul_smul, div_eq_inv_mul] using congrArg ((2 : ℝ)⁻¹ • ·) hst
    have hs' : s / 2 ∈ Set.Ioo 0 (1 / 3) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have ht' : t / 2 ∈ Set.Ioo 0 (1 / 3) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq : (if e.2 then 1 - s else s) = (if e.2 then 1 - s / 2 else s / 2) :=
      AffineMap.lineMap_injective ℝ (hab e.1)
        (hinter e.1 k.1 hne (hit hs ht hst) (hit hs' ht' hhalf))
    by_cases htag : e.2 = true <;>
      simp only [htag, Bool.false_eq_true, ↓reduceIte] at heq <;> linarith [hs.1]
  rcases e with ⟨i, tag⟩
  rcases k with ⟨j, other⟩
  change i = j at hindex
  subst j
  cases tag <;> cases other
  · rfl
  · exact (hab i hp).elim
  · exact (hab i hp.symm).elim
  · rfl

end Cslib.Polygonal
