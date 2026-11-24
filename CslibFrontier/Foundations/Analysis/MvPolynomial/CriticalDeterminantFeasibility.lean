/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, real multivariate polynomial minima)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ShiftedLabel
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalIntegerSpecialization
public import Mathlib.Data.Nat.Size
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseRootDeterminant
import CslibFrontier.Foundations.Analysis.MvPolynomial.CriticalRootFeasibility
import CslibFrontier.Foundations.Data.MvPolynomial.PolynomialEvaluationBounds

/-!
# A finite determinant test for real feasibility

A nonnegative integer polynomial has a real zero exactly when a bounded shift and a short
derivative-sign list give a negative multiplication determinant in its critical quotient.
The input degree and coefficient norm determine the specialization, cutoff and label bounds.

Adapted from `FiniteCriticalCriterion.real_zero_iff_negative_finiteCriticalDeterminant` in
lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`. Here `ell` is the source's `d + 1`,
and the norm and specialization exponents come from the library's coefficient bounds.
The same bounds control the degree and coefficient norm of each shifted label used
in the determinant.
-/

public section

namespace MvPolynomial.CriticalSystem

open PurePower
open scoped Polynomial

/-- The common power-of-two coefficient norm exponent for the integer critical-value
polynomial and its cutoff test. -/
@[expose] def criticalRootLabelCoeffNormExponent (n ell b : ℕ) : ℕ :=
  let H := parametricValueCoeffNormExponent n ell b
  max (H + criticalParameterExponent n ell b * (ell ^ n * (ell + 2 + n * ell))) (H + 2)

private theorem criticalRootLabel_dimension_le (n ell : ℕ) :
    ell ^ n ≤ 2 ^ (n * ell.size) :=
  (Nat.pow_le_pow_left (Nat.lt_size_self ell).le n).trans_eq
    (by rw [← pow_mul, Nat.mul_comm])

private theorem criticalRootLabel_inputs_bounds {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b) :
    let H := parametricValueCoeffNormExponent n ell b
    let q := Polynomial.C ((2 : ℤ) ^ (H + 1)) - Polynomial.X
    let p := valuePolynomial (by omega : 1 ≤ ell) (fun i => (separatedCenters ell i : ℤ))
      (2 ^ criticalParameterExponent n ell b) F hF
    let B := criticalRootLabelCoeffNormExponent n ell b
    q.natDegree ≤ ell ^ n ∧ q.coeffNorm1 ≤ 2 ^ B ∧ p.coeffNorm1 ≤ 2 ^ B := by
  intro H q p B
  have hD : 0 < ell ^ n := pow_pos (by omega) _
  have hqD : q.natDegree ≤ ell ^ n := (Polynomial.natDegree_sub_le _ _).trans
    (by simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_le, max_eq_right]
      using Nat.succ_le_of_lt hD)
  refine ⟨hqD, ?_, (coeffNorm1_valuePolynomial_at_pow_two_le hell F hF hb _).trans
    (Nat.pow_le_pow_right (by decide) (le_max_left _ _))⟩
  have hR : ((2 : ℤ) ^ (H + 1)).natAbs = 2 ^ (H + 1) := by
    rw [Int.natAbs_pow]
    rfl
  apply (Polynomial.coeffNorm1_sub_le _ _).trans
  rw [Polynomial.coeffNorm1_C, Polynomial.coeffNorm1_X, hR]
  refine le_trans ?_ (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [show H + 2 = (H + 1) + 1 by rfl, pow_succ]
  have := Nat.one_le_two_pow (n := H + 1)
  omega

/-- The shifted sparse label for the actual critical-value polynomial and the test for
lying below the cutoff. -/
@[expose] noncomputable def criticalShiftedRootLabel {n ell : ℕ} (hell : 1 ≤ ell) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell)
    (L : List (Fin (ell ^ n) × SignType)) (e : ℕ) : ℤ[X] :=
  let a : Fin n → ℤ := fun i => separatedCenters ell i
  let u : ℤ := 2 ^ criticalParameterExponent n ell b
  let R : ℤ := 2 ^ (parametricValueCoeffNormExponent n ell b + 1)
  Polynomial.shiftedRootLabel (ell ^ n) e
    (Polynomial.sparseIntegerRootLabel (valuePolynomial hell a u F hF)
      (Polynomial.C R - Polynomial.X) (n * ell.size) (criticalRootLabelCoeffNormExponent n ell b) L)

/-- Degree and coefficient norm bounds for the shifted critical label, uniform in the
derivative-sign list. This adapts `FiniteCriticalNormBounds.finiteCriticalShiftedLabel_bounds`
from the pinned lean-canny revision above, with the label length bound used for the
shift's coefficient allowance. -/
theorem criticalShiftedRootLabel_bounds {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (L : List (Fin (ell ^ n) × SignType)) {e : ℕ} (he : e ≤ ell ^ n) :
    let D := ell ^ n
    let N := n * ell.size
    let B := criticalRootLabelCoeffNormExponent n ell b
    let s := Polynomial.derivativeRootLabelPrecision D B
    let g := criticalShiftedRootLabel (by omega) b F hF L e
    g.natDegree ≤ Polynomial.signLabelDegreeBound (N + 1) s D ∧
      g.coeffNorm1 ≤ 2 ^ (Polynomial.signLabelNormExponent (N + 1) s
        (Polynomial.iterateDerivativeNormExponent D B) + N + 3) := by
  intro D N B s g
  obtain ⟨hqD, hqb, hpb⟩ := criticalRootLabel_inputs_bounds hell F hF hb
  have hpD := (valuePolynomial_natDegree (by omega : 1 ≤ ell)
    (fun i => (separatedCenters ell i : ℤ)) (2 ^ criticalParameterExponent n ell b) F hF).le
  obtain ⟨hdegree, hnorm⟩ := Polynomial.sparseIntegerRootLabel_bounds L hpD hqD hpb hqb
  obtain ⟨hsdegree, hsnorm⟩ := Polynomial.shiftedRootLabel_bounds _ he
    (criticalRootLabel_dimension_le n ell) hnorm
  exact ⟨hsdegree.trans hdegree, hsnorm⟩

/-- Total-degree budget for the shifted label evaluated at the integer critical objective. -/
@[expose] def criticalLabelObjectiveDegreeBound (n ell b : ℕ) : ℕ :=
  let D := ell ^ n
  let N := n * ell.size
  let B := criticalRootLabelCoeffNormExponent n ell b
  let s := Polynomial.derivativeRootLabelPrecision D B
  Polynomial.signLabelDegreeBound (N + 1) s D * (ell + 1)

/-- Binary coefficient-norm budget for the shifted label evaluated at the integer critical
objective. -/
@[expose] def criticalLabelObjectiveCoeffNormExponent (n ell b : ℕ) : ℕ :=
  let D := ell ^ n
  let N := n * ell.size
  let B := criticalRootLabelCoeffNormExponent n ell b
  let s := Polynomial.derivativeRootLabelPrecision D B
  let d := Polynomial.signLabelDegreeBound (N + 1) s D
  let k := Polynomial.signLabelNormExponent (N + 1) s
    (Polynomial.iterateDerivativeNormExponent D B) + N + 3
  let bv := criticalSystemCoeffNormExponent n ell b + criticalParameterExponent n ell b
  k + bv * d

/-- Evaluating the shifted label at the integer critical objective multiplies the label's
degree bound by `ell + 1`. The specialization bound supplies the objective's coefficient
allowance for the composed polynomial. -/
theorem criticalLabelObjective_bounds {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (L : List (Fin (ell ^ n) × SignType)) {e : ℕ} (he : e ≤ ell ^ n) :
    let u := criticalParameterExponent n ell b
    let v := deformedPolynomial ell (fun i => (separatedCenters ell i : ℤ)) (2 ^ u) F
    let w := Polynomial.aeval v (criticalShiftedRootLabel (by omega) b F hF L e)
    w.totalDegree ≤ criticalLabelObjectiveDegreeBound n ell b ∧
      w.coeffNorm1 ≤ 2 ^ criticalLabelObjectiveCoeffNormExponent n ell b := by
  intro u v w
  let bv := criticalSystemCoeffNormExponent n ell b + u
  let g := criticalShiftedRootLabel (by omega : 1 ≤ ell) b F hF L e
  obtain ⟨hdeg, hnorm⟩ := criticalShiftedRootLabel_bounds hell F hF hb L he
  have hvdeg : v.totalDegree ≤ ell + 1 :=
    totalDegree_deformedPolynomial_le ell _ _ _ (hF.trans (Nat.le_succ _))
  have hv : v.coeffNorm1 ≤ 2 ^ bv :=
    (criticalSystem_coeffNorm1_at_pow_two_le (by omega) F hF hb u).2
  refine ⟨(Polynomial.totalDegree_aeval_mvPolynomial_le g v).trans
    (Nat.mul_le_mul hdeg hvdeg), ?_⟩
  refine (Polynomial.coeffNorm1_aeval_mvPolynomial_le g v Nat.one_le_two_pow hv).trans ?_
  exact (Nat.mul_le_mul hnorm (Nat.pow_le_pow_right Nat.one_le_two_pow hdeg)).trans_eq
    (by rw [← pow_mul, ← pow_add, criticalLabelObjectiveCoeffNormExponent])

/-- The determinant of multiplication by the label evaluated at the deformed objective
in the integer critical quotient. -/
@[expose] noncomputable def criticalLabelDeterminant {n ell : ℕ} (hell : 1 ≤ ell) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell)
    (L : List (Fin (ell ^ n) × SignType)) (e : ℕ) : ℤ :=
  let a : Fin n → ℤ := fun i => separatedCenters ell i
  let u : ℤ := 2 ^ criticalParameterExponent n ell b
  (multiplicationMatrix hell (criticalLower ell a u F) (criticalLower_degree ell hell a u F hF)
    (Polynomial.aeval (deformedPolynomial ell a u F)
      (criticalShiftedRootLabel hell b F hF L e))).det

/-- Binary magnitude budget for the finite feasibility determinant. -/
@[expose] def criticalLabelDeterminantExponent (n ell b : ℕ) : ℕ :=
  multiplicationMatrixCharpolyCoeffNormExponent n ell (criticalLabelObjectiveDegreeBound n ell b)
    (criticalLabelObjectiveCoeffNormExponent n ell b)
    (criticalSystemCoeffNormExponent n ell b + criticalParameterExponent n ell b)

/-- The determinant in the finite feasibility criterion is bounded solely by the arity,
degree and coefficient budget of the integer input, uniformly over bounded shifts.
Adapted from `FiniteCriticalNormBounds.finiteCriticalDeterminant_natAbs_le` in the
pinned lean-canny revision above. -/
theorem natAbs_criticalLabelDeterminant_le {n ell b : ℕ} (hell : 2 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (L : List (Fin (ell ^ n) × SignType)) {e : ℕ} (he : e ≤ ell ^ n) :
    (criticalLabelDeterminant (by omega) b F hF L e).natAbs ≤
      2 ^ criticalLabelDeterminantExponent n ell b := by
  let a : Fin n → ℤ := fun i => separatedCenters ell i
  let u : ℤ := 2 ^ criticalParameterExponent n ell b
  let w := Polynomial.aeval (deformedPolynomial ell a u F)
    (criticalShiftedRootLabel (by omega : 1 ≤ ell) b F hF L e)
  obtain ⟨hdeg, hnorm⟩ := criticalLabelObjective_bounds hell F hF hb L he
  exact natAbs_multiplicationMatrix_det_le_pow_two hell (criticalLower ell a u F)
    (criticalLower_degree ell (by omega) a u F hF)
    (criticalSystem_coeffNorm1_at_pow_two_le (by omega) F hF hb _).1 w hdeg hnorm

/-- A nonnegative polynomial satisfying the given bounds has a real zero exactly when
a short derivative-sign list and a bounded shift make its critical quotient determinant
negative. -/
theorem exists_zero_iff_exists_neg_criticalLabelDeterminant {n ell b : ℕ}
    (hell : 2 ≤ ell) (he : Even (ell + 1)) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ ell) (hb : F.coeffNorm1 ≤ 2 ^ b)
    (hFn : ∀ x, 0 ≤ eval x (F.map (Int.castRingHom ℝ))) :
    (∃ x, eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ L : List (Fin (ell ^ n) × SignType), L.length ≤ n * ell.size ∧
        ∃ e : ℕ, e ≤ ell ^ n ∧ criticalLabelDeterminant (by omega) b F hF L e < 0 := by
  have hell' : 1 ≤ ell := by omega
  let a : Fin n → ℤ := fun i => separatedCenters ell i
  let u : ℤ := 2 ^ criticalParameterExponent n ell b
  let H := parametricValueCoeffNormExponent n ell b
  let R : ℤ := 2 ^ (H + 1)
  let q : ℤ[X] := Polynomial.C R - Polynomial.X
  let v := deformedPolynomial ell a u F
  let μ := multiplicationMatrix hell' (criticalLower ell a u F)
    (criticalLower_degree ell hell' a u F hF)
  let M := μ v
  let B := criticalRootLabelCoeffNormExponent n ell b
  have hcard : Fintype.card (NormalIndex n ell) = ell ^ n := by simp [NormalIndex]
  have hD : 0 < ell ^ n := pow_pos (by omega) _
  obtain ⟨hqD, hqb, hMb⟩ := criticalRootLabel_inputs_bounds hell F hF hb
  have hsepR : (M.charpoly.map (Int.castRingHom ℝ)).Separable :=
    (valuePolynomial_at_integerParameterExclusion hell F hF hb).1
  have hsep := hsepR.map (f := Complex.ofRealHom)
  rw [Polynomial.map_map] at hsep
  have hcast : Complex.ofRealHom.comp (Int.castRingHom ℝ) = algebraMap ℤ ℂ := by
    ext z
    simp
  rw [hcast] at hsep
  have hgeometry := exists_zero_iff_exists_root_lt_at_integerParameterExclusion hell he F hF hb hFn
  have hroot : (∃ x, eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ x : ℝ, M.charpoly.eval₂ (Int.castRingHom ℝ) x = 0 ∧
        0 < q.eval₂ (Int.castRingHom ℝ) x := by
    simpa only [q, Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X,
      sub_pos, Int.coe_castRingHom, R, Int.cast_pow, Int.cast_ofNat, Polynomial.IsRoot,
      Polynomial.eval_map, and_comm, valuePolynomial, a, u, H, M, μ, v] using hgeometry
  refine hroot.trans ?_
  simpa only [Polynomial.aeval_algHom_apply, criticalLabelDeterminant, criticalShiftedRootLabel,
    valuePolynomial, a, u, H, R, q, B, M, μ, v] using
    (Matrix.exists_eval₂_pos_at_charpoly_root_iff_neg_shiftedRootLabel_det
      M hD hcard.le (criticalRootLabel_dimension_le n ell) hqD hMb hqb hsep)

end MvPolynomial.CriticalSystem
