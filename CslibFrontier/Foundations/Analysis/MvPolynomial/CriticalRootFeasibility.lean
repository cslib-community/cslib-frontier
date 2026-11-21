/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalIntegerSpecialization
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalValueCutoff
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees

/-!
# A characteristic-root test for real feasibility

A nonnegative integer polynomial has a real zero exactly when its integer quotient
characteristic polynomial, specialized at the chosen power-of-two parameter, has a real root
below the value cutoff. The minimum gives a root in the forward direction. Separability lets
every real root be realized at a critical point, whose value bounds the minimum from above.

Adapted from `CriticalFeasibility` and `LargeSpecializationBounds` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. The statement uses the integer polynomial supplied
by the specialization construction.
-/

public section

namespace MvPolynomial.CriticalSystem

open PurePower

/-- Under the degree and coefficient bounds, a nonnegative integer polynomial has a real
zero exactly when the chosen integer critical-value polynomial has a real root strictly
below the chosen value cutoff. -/
theorem exists_zero_iff_exists_root_lt_at_integerParameterExclusion {n ell b : ℕ}
    (hell : 2 ≤ ell) (he : Even (ell + 1)) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (hFn : ∀ x, 0 ≤ eval x (F.map (Int.castRingHom ℝ))) :
    let H := parametricValueCoeffNormExponent n ell b
    let q := valuePolynomial (by omega : 1 ≤ ell) (fun i => (separatedCenters ell i : ℤ))
      (2 ^ criticalParameterExponent n ell b) F hF
    (∃ x, eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ η : ℝ, η < 2 ^ (H + 1) ∧ (q.map (Int.castRingHom ℝ)).IsRoot η := by
  intro H q
  let a : Fin n → ℝ := fun i => separatedCenters ell i
  let u : ℝ := 2 ^ criticalParameterExponent n ell b
  let G := F.map (Int.castRingHom ℝ)
  have hell' : 1 ≤ ell := by omega
  have ha (i : Fin n) : 0 ≤ a i := Nat.cast_nonneg _
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hG : G.totalDegree ≤ ell := (totalDegree_map_le (Int.castRingHom ℝ) F).trans hF
  have hq : q.map (Int.castRingHom ℝ) = valuePolynomial hell' a u G hG := by
    simp only [q, valuePolynomial_map, Int.coe_castRingHom, Int.cast_natCast, Int.cast_pow,
      Int.cast_ofNat, a, u, G]
  have hsep : (q.map (Int.castRingHom ℝ)).Separable :=
    (valuePolynomial_at_integerParameterExclusion hell F hF hb).1
  rw [hq] at hsep ⊢
  have hcut : (∃ x, eval x G = 0) ↔ criticalMinimumValue ell a G u < 2 ^ (H + 1) :=
    exists_zero_iff_criticalMinimumValue_lt_at_parameterExclusion hell' he F hF hFn
      (parametricValuePolynomial_bivariateCoeffNorm1_le hell F hF hb)
  constructor
  · intro hz
    exact ⟨_, hcut.mp hz, isRoot_valuePolynomial_criticalMinimumValue hell' he a ha G hG hFn u hu⟩
  · rintro ⟨η, hη, hroot⟩
    have hnonzero := (valuePolynomial_monic hell' a u G hG).ne_zero
    have hsimple : (valuePolynomial hell' a u G hG).rootMultiplicity η = 1 :=
      le_antisymm (Polynomial.rootMultiplicity_le_one_of_separable hsep η)
        (Nat.succ_le_of_lt ((Polynomial.rootMultiplicity_pos hnonzero).mpr hroot))
    obtain ⟨x, _, hx⟩ := exists_common_zero_of_rootMultiplicity_multiplicationMatrix_eq_one
      hell' (criticalLower ell a u G) (criticalLower_degree ell hell' a u G hG)
      (deformedPolynomial ell a u G) hsimple
    have hx' : eval x (deformedPolynomial ell a u G) = η := by
      simpa only [aeval_eq_eval] using hx
    obtain ⟨y, hy⟩ := exists_isMinOn_eval_deformedPolynomial ell hell' he a ha G hFn u hu
    apply hcut.mpr
    rw [criticalMinimumValue_eq_of_isMinOn ell a G u hy]
    exact (hy (Set.mem_univ x)).trans_lt (hx'.trans_lt hη)

end MvPolynomial.CriticalSystem
