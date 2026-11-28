/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root products)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Complex.Module
import CslibFrontier.Foundations.Analysis.Complex.ConjugateProduct

/-!
# Products of real polynomial values over distinct complex roots

For real polynomials, the product over distinct complex roots factors into
the product over distinct real roots and the squared norms from the upper
half-plane. This identifies the nonreal contribution to the spectral sign.

Adapted from `RealRootProducts` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset
open scoped ComplexConjugate

/-- Evaluating a real polynomial on the distinct complex roots of another real
polynomial gives one real factor per real root and one squared norm per nonreal pair. -/
theorem prod_aeval_aroots_toFinset_eq (p g : Polynomial ℝ) :
    (∏ z ∈ (p.aroots ℂ).toFinset, aeval z g) =
      (((∏ x ∈ p.roots.toFinset, g.eval x) *
        ∏ z ∈ (p.aroots ℂ).toFinset.filter (fun z => 0 < z.im),
          Complex.normSq (aeval z g) : ℝ) : ℂ) := by
  classical
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  let roots := (p.aroots ℂ).toFinset
  have hmap : p.map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hp
  have hmem (z : ℂ) : z ∈ roots ↔ aeval z p = 0 := by simp [roots, hmap]
  have eval_coe (q : Polynomial ℝ) (x : ℝ) : aeval (x : ℂ) q = ((q.eval x : ℝ) : ℂ) :=
    aeval_algHom_apply Complex.ofRealAm x q
  have eval_conj (q : Polynomial ℝ) (z : ℂ) : aeval (conj z) q = conj (aeval z q) :=
    aeval_algHom_apply Complex.conjAe z q
  have hconj (z : ℂ) (hz : z ∈ roots) : conj z ∈ roots := by simp [hmem, eval_conj, (hmem z).mp hz]
  have hreal : p.roots.toFinset.image (fun x : ℝ => (x : ℂ)) =
      roots.filter (fun z => z.im = 0) := by
    ext z
    rw [mem_image, mem_filter, hmem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hp] at hx
      exact ⟨by rw [eval_coe, hx.eq_zero, Complex.ofReal_zero], Complex.ofReal_im x⟩
    · rintro ⟨hz, him⟩
      have he := Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr him)
      refine ⟨z.re, Multiset.mem_toFinset.mpr ((mem_roots hp).mpr ?_), he⟩
      rwa [IsRoot.def, ← Complex.ofReal_eq_zero, ← eval_coe, he]
  rw [Complex.prod_eq_ofReal_mul_prod_normSq roots (fun z => aeval z g) hconj
    (fun z _ => eval_conj g z), ← hreal, prod_image Complex.ofReal_injective.injOn]
  simp only [eval_coe, Complex.ofReal_re, roots]

end Polynomial
