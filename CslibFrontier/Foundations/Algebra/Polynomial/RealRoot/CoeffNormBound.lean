/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root bounds)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.CoeffNorm1
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Real root bounds from the integer coefficient norm

Cauchy's bound implies that a real root of a nonzero integer polynomial has absolute value
strictly less than its coefficient ℓ₁ norm plus one. The leading coefficient has norm at least
one. This is the bound used for exclusion of exceptional parameters in lean-canny.
-/

public section

namespace Polynomial

/-- Every real root has absolute value less than the integer coefficient norm plus one. -/
theorem abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero {p : Polynomial ℤ} (hp : p ≠ 0) {x : ℝ}
    (hx : p.eval₂ (Int.castRingHom ℝ) x = 0) : |x| < (p.coeffNorm1 : ℝ) + 1 := by
  let f := Int.castRingHom ℝ
  have hf : Function.Injective f := Int.cast_injective
  let q := p.map f
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  have hroot : q.IsRoot x := by simpa only [IsRoot.def, q, eval_map] using hx
  have hnorm (a : ℤ) : ‖f a‖ = (a.natAbs : ℝ) := by
    change ‖(a : ℝ)‖ = _
    rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hl : (1 : ℝ) ≤ ‖q.leadingCoeff‖ := by
    rw [show q.leadingCoeff = f p.leadingCoeff from leadingCoeff_map_of_injective hf p, hnorm]
    have hn := Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  let s := (Finset.range q.natDegree).sup (fun i => ‖q.coeff i‖₊)
  have hs : (s : ℝ) ≤ p.coeffNorm1 := by
    have hsup : s ≤ (p.coeffNorm1 : NNReal) := by
      refine Finset.sup_le fun i _ => ?_
      rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_natCast,
        show q.coeff i = f (p.coeff i) from coeff_map f i, hnorm]
      exact_mod_cast natAbs_coeff_le_coeffNorm1 p i
    exact_mod_cast hsup
  have hx' : ‖x‖ < (q.cauchyBound : ℝ) := hroot.norm_lt_cauchyBound hq
  rw [Real.norm_eq_abs] at hx'
  refine hx'.trans_le ?_
  rw [cauchyBound, NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, coe_nnNorm]
  exact add_le_add ((div_le_self (by positivity) hl).trans hs) le_rfl

end Polynomial
