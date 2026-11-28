/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalParameterExclusion
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueCoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree

/-!
# Integer specialization of critical values

Specializing the symbolic critical-value polynomial gives the actual integer quotient
characteristic polynomial. Its coefficient norm at a power of two is bounded in terms of
the input coefficient-norm exponent and the exponent of that power. At the parameter chosen
from the symbolic norm bound, its real image is separable and avoids the value cutoff.

Adapted from `BoundedCriticalFeasibility` and `IntegerCriticalSpecialization` in lean-canny
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. This uses the arbitrary-ring specialization
identity for the actual quotient and the coefficient-dependent parameter-degree estimate.
-/

public section

namespace MvPolynomial.CriticalSystem

/-- The power-of-two parameter exponent derived from arity, pure-power degree, and an input
coefficient-norm bound of `2 ^ b`. -/
@[expose] def criticalParameterExponent (n ell b : ℕ) : ℕ :=
  Polynomial.parameterExclusionExponent (ell ^ n) (parametricValueCoeffNormExponent n ell b)

/-- At parameter `2 ^ s`, the specialized lower relations and deformed objective share
the symbolic coefficient norm allowance plus `s` bits. This is the specialization step
of `FiniteCriticalMassBounds` in the pinned lean-canny revision above. -/
theorem criticalSystem_coeffNorm1_at_pow_two_le {n ell b : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (s : ℕ) :
    let a : Fin n → ℤ := fun i => separatedCenters ell i
    let u : ℤ := 2 ^ s
    let bound := 2 ^ (criticalSystemCoeffNormExponent n ell b + s)
    (∀ i, (criticalLower ell a u F i).coeffNorm1 ≤ bound) ∧
      (deformedPolynomial ell a u F).coeffNorm1 ≤ bound := by
  intro a u bound
  let R := criticalSystemCoeffNormExponent n ell b
  have hu : u.natAbs = 2 ^ s := Int.natAbs_pow 2 s
  have hcomp : (Polynomial.evalRingHom u).comp Polynomial.C = RingHom.id ℤ := by
    ext
    simp
  have specialize (p : MvPolynomial (Fin n) (Polynomial ℤ))
      (hp : HasParameterDegree p 1) (hn : ParameterCoeffNorm.norm p ≤ 2 ^ R) :
      (p.map (Polynomial.evalRingHom u)).coeffNorm1 ≤ bound := by
    have h := ParameterCoeffNorm.coeffNorm1_map_evalRingHom_le p u
      (hu.symm ▸ Nat.one_le_two_pow) hp
    rw [hu, pow_one] at h
    exact h.trans ((Nat.mul_le_mul_right _ hn).trans_eq (pow_add 2 _ _).symm)
  obtain ⟨hrdeg, hvdeg⟩ := criticalSystem_hasParameterDegree ell F
  obtain ⟨hrnorm, hvnorm⟩ := criticalSystem_norm_le hell F hF hb
  exact ⟨fun i => by
      simpa only [criticalLower_map, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.eval_X, MvPolynomial.map_map, hcomp, MvPolynomial.map_id, a] using
        specialize _ (hrdeg i) (hrnorm i),
    by simpa only [deformedPolynomial_map, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.eval_X, MvPolynomial.map_map, hcomp, MvPolynomial.map_id, a] using
        specialize _ hvdeg hvnorm⟩

/-- Bound the integer characteristic polynomial's coefficient norm at parameter `2 ^ s`.
The exponent includes the symbolic norm allowance and `s` times the parameter-degree bound. -/
theorem coeffNorm1_valuePolynomial_at_pow_two_le {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b) (s : ℕ) :
    (valuePolynomial (by omega : 1 ≤ ell) (fun i => (separatedCenters ell i : ℤ))
      (2 ^ s) F hF).coeffNorm1 ≤
        2 ^ (parametricValueCoeffNormExponent n ell b + s * (ell ^ n * (ell + 2 + n * ell))) := by
  let q := parametricValuePolynomial (by omega : 1 ≤ ell) F hF
  let D := ell ^ n * (ell + 2 + n * ell)
  have hd (k : ℕ) : (q.coeff k).natDegree ≤ D :=
    (natDegree_parametricValuePolynomial_coeff_le hell F hF k).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
  have ha : ((2 : ℤ) ^ s).natAbs = 2 ^ s := Int.natAbs_pow 2 s
  rw [← parametricValuePolynomial_map_evalRingHom]
  have h := Polynomial.coeffNorm1_map_evalRingHom_le q ((2 : ℤ) ^ s)
    (ha.symm ▸ Nat.one_le_two_pow) hd
  rw [ha] at h
  exact h.trans ((Nat.mul_le_mul_right _ (parametricValuePolynomial_bivariateCoeffNorm1_le
    hell F hF hb)).trans_eq (by rw [← pow_mul, ← pow_add]))

/-- The quotient characteristic polynomial at the chosen integer parameter becomes
separable over the reals and does not vanish at the cutoff. -/
theorem valuePolynomial_at_integerParameterExclusion {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b) :
    let H := parametricValueCoeffNormExponent n ell b
    let a : ℤ := 2 ^ (H + 1)
    let u : ℤ := 2 ^ criticalParameterExponent n ell b
    let q := valuePolynomial (by omega : 1 ≤ ell) (fun i => (separatedCenters ell i : ℤ)) u F hF
    let q' := q.map (Int.castRingHom ℝ)
    q'.Separable ∧ q'.eval (a : ℝ) ≠ 0 := by
  intro H a u q q'
  have hφ : (Int.castRingHom ℝ).comp (Polynomial.evalRingHom u) =
      Polynomial.eval₂RingHom (Int.castRingHom ℝ) (u : ℝ) := by
    ext <;> simp [Polynomial.coe_evalRingHom, Polynomial.coe_eval₂RingHom]
  dsimp only [q', q]
  rw [← parametricValuePolynomial_map_evalRingHom, Polynomial.map_map, hφ]
  simpa only [u, H, a, criticalParameterExponent, Int.cast_pow, Int.cast_ofNat] using
    parametricValuePolynomial_at_parameterExclusion (by omega : 1 ≤ ell) F hF
      (parametricValuePolynomial_bivariateCoeffNorm1_le hell F hF hb)

end MvPolynomial.CriticalSystem
