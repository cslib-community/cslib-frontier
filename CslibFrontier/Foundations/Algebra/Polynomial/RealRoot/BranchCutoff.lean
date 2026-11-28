/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root bounds)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.CoeffNormBound
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# A finite cutoff for monotone algebraic root branches

View an integer bivariate polynomial as a polynomial in the parameter whose coefficients are
polynomials in the branch value. A bounded nondecreasing root branch converges to a root of the
leading coefficient. A continuous branch below a cutoff stays below it once the polynomial
specialized at that cutoff has no further roots in the parameter. The integer coefficient norm
gives explicit thresholds for both facts.

Adapted from `PolynomialBranchLimit`, `AlgebraicMinimumThreshold`, and
`IntegerAlgebraicThreshold` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
The filter formulation adapts `PolynomialFilteredLimit` at the same revision.
-/

public section

namespace Polynomial

open Filter Set
open scoped Topology

private theorem continuous_eval₂_eval₂RingHom (P : Polynomial (Polynomial ℤ)) :
    Continuous (fun z : ℝ × ℝ =>
      P.eval₂ (eval₂RingHom (Int.castRingHom ℝ) z.1) z.2) := by
  simp only [eval₂_eq_sum, Polynomial.sum]
  apply continuous_finsetSum
  intro i _
  exact ((P.coeff i).continuous_eval₂ (Int.castRingHom ℝ)).comp continuous_fst |>.mul
    (continuous_snd.pow i)

/-- Along a nontrivial filter, a convergent family of roots limits to a root of the
leading parameter coefficient when the parameter tends to positive infinity. -/
theorem eval₂_leadingCoeff_eq_zero_of_tendsto_atTop {ι : Type*} {l : Filter ι} [NeBot l]
    (P : Polynomial (Polynomial ℤ)) {u m : ι → ℝ} {L : ℝ}
    (hu : Tendsto u l atTop) (hm : Tendsto m l (𝓝 L))
    (hroot : ∀ᶠ k in l, P.eval₂ (eval₂RingHom (Int.castRingHom ℝ) (m k)) (u k) = 0) :
    P.leadingCoeff.eval₂ (Int.castRingHom ℝ) L = 0 := by
  have ht : Tendsto (fun k => (m k, (u k)⁻¹)) l (𝓝 (L, 0)) :=
    hm.prodMk_nhds (tendsto_inv_atTop_zero.comp hu)
  have hc := (continuous_eval₂_eval₂RingHom P.reverse).continuousAt.tendsto.comp ht
  have hz : ∀ᶠ k in l,
      P.reverse.eval₂ (eval₂RingHom (Int.castRingHom ℝ) (m k)) (u k)⁻¹ = 0 := by
    filter_upwards [hu.eventually_gt_atTop (0 : ℝ), hroot] with k hpos hzero
    let := invertibleOfNonzero hpos.ne'
    simpa only [invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (eval₂RingHom (Int.castRingHom ℝ) (m k)) (u k) P).mpr hzero
  have he := tendsto_nhds_unique hc (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  simpa only [eval₂_at_zero, coeff_zero_reverse, coe_eval₂RingHom] using he

/-- A continuous nondecreasing branch of real roots is bounded above on the nonnegative
half-line exactly when its value at `U` is below `R`. The cutoff `R` exceeds the absolute
values of the roots of the leading coefficient in the parameter. The parameter `U` exceeds
the absolute values of the roots after substituting `R` for the branch value. -/
theorem bounded_root_branch_iff_lt {P : Polynomial (Polynomial ℤ)} (hP : P ≠ 0)
    {m : ℝ → ℝ} (hm : MonotoneOn m (Ici 0)) (hc : ContinuousOn m (Ici 0))
    (hroot : ∀ u : ℝ, 0 < u → P.eval₂ (eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0)
    {R : ℤ} (hR : (P.leadingCoeff.coeffNorm1 : ℝ) + 1 ≤ (R : ℝ))
    {U : ℝ} (hU : ((P.map (evalRingHom R)).coeffNorm1 : ℝ) + 1 ≤ U) :
    (∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → m u ≤ B) ↔ m U < (R : ℝ) := by
  have hpos : 0 < U := lt_of_lt_of_le (by positivity) hU
  constructor
  · rintro ⟨B, hB⟩
    let f (u : ℝ) := m (max u 0)
    have hf : Monotone f := fun u v huv =>
      hm (le_max_right u 0) (le_max_right v 0) (max_le_max huv le_rfl)
    have hb : BddAbove (range f) := ⟨B, by
      rintro _ ⟨u, rfl⟩
      exact hB _ (le_max_right u 0)⟩
    let L := ⨆ u, f u
    have hlim : Tendsto m atTop (𝓝 L) := by
      apply (tendsto_atTop_ciSup hf hb).congr'
      exact (eventually_ge_atTop (0 : ℝ)).mono fun u hu => congrArg m (max_eq_left hu)
    have hz := eval₂_leadingCoeff_eq_zero_of_tendsto_atTop P tendsto_id hlim
      ((eventually_gt_atTop (0 : ℝ)).mono hroot)
    have hL := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero (leadingCoeff_ne_zero.mpr hP) hz
    have hle : m U ≤ L := by
      simpa only [f, max_eq_left hpos.le] using le_ciSup hb U
    exact hle.trans_lt ((le_abs_self L).trans_lt (hL.trans_le hR))
  · intro hstart
    let S := P.map (evalRingHom R)
    have hS : S ≠ 0 := by
      intro hz
      have hcoeff : P.leadingCoeff.eval R = 0 := by
        simpa only [S, coeff_map, coe_evalRingHom, coeff_natDegree, coeff_zero] using
          congrArg (fun p : Polynomial ℤ => p.coeff P.natDegree) hz
      have hr : P.leadingCoeff.eval₂ (Int.castRingHom ℝ) (R : ℝ) = 0 := by
        change P.leadingCoeff.eval₂ (Int.castRingHom ℝ) ((Int.castRingHom ℝ) R) = 0
        rw [eval₂_at_apply, hcoeff, map_zero]
      have habs := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero (leadingCoeff_ne_zero.mpr hP) hr
      exact (not_lt_of_ge hR) ((le_abs_self (R : ℝ)).trans_lt habs)
    refine ⟨(R : ℝ), fun u hu => ?_⟩
    by_cases hle : u ≤ U
    · exact (hm hu hpos.le hle).trans hstart.le
    · have hUu := (lt_of_not_ge hle).le
      by_contra! hgt
      obtain ⟨v, hv, he⟩ := intermediate_value_Icc hUu
        (hc.mono fun x hx => hpos.le.trans hx.1) ⟨hstart.le, hgt.le⟩
      have hzero := hroot v (hpos.trans_le hv.1)
      rw [he] at hzero
      have hsection : S.eval₂ (Int.castRingHom ℝ) v = 0 := by
        rw [show S = P.map (evalRingHom R) from rfl, eval₂_map, ← hzero]
        congr 1
        ext <;> simp
      have habs := abs_lt_coeffNorm1_add_one_of_eval₂_eq_zero hS hsection
      exact (not_lt_of_ge (hU.trans hv.1)) ((le_abs_self v).trans_lt habs)

end Polynomial
