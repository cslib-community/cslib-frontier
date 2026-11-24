/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Complexity.RealAlgebraic.CharacteristicCoefficients
import CslibFrontier.Foundations.Data.MvPolynomial.LowestComponent
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueCoeffNorm
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValueParameterDegree
import Mathlib.Tactic.NormNum

/-! # Characteristic-coefficient evaluator edge cases and uniform certificates -/

public section
namespace CslibFrontierTests.RealAlgebraicCharacteristic

open Cslib Cslib.Complexity Cslib.Complexity.RealAlgebraic Turing.MultiTapeTM Polynomial

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The logarithm's zero slot is masked before inversion, including at the smallest prime.
example (t : ℕ) : traceLogarithmResidue 2 0 t = 0 := by
  simp [traceLogarithmResidue]

-- The total default above the dimension does not depend on any primality hypothesis.
example (p : ℕ) (t : ℕ → ℕ) : traceExponentialCoefficient p 0 1 t = 0 := by
  simp [traceExponentialCoefficient]

-- The factorial evaluator includes 0!, and the below-prime denominator is invertible.
example : (factorialResidue 2 0 : ZMod 2) = 1 := by
  rw [factorialResidue_cast]
  norm_num

example : (powMod 3 (factorialResidue 3 2) (3 - 2) : ZMod 3) = (2 : ZMod 3)⁻¹ := by
  simpa using (factorialResidue_inverse (p := 3) (j := 2) (by decide))

-- The empty matrix works at p=2 with an arbitrary, ignored trace slot zero.
theorem emptyMatrix (t : ℕ → ℕ) : traceExponentialCoefficient 2 0 0 t = 1 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 2) (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) (by decide) 0 t
    (by intro k hk h; simp only [Fintype.card_fin] at h; omega)
  simpa [Matrix.charpoly_isEmpty, ZMod.val_one_eq_one_mod] using h

-- For a 1-by-1 identity matrix over F_3, the characteristic polynomial is X-1.
example : traceExponentialCoefficient 3 1 0 (fun _ => 1) = 2 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 3) (1 : Matrix (Fin 1) (Fin 1) (ZMod 3)) (by decide) 0 (fun _ => 1)
    (by intro k _ _; simp)
  simpa [Matrix.charpoly_one, ZMod.val_neg_one] using h

example : traceExponentialCoefficient 3 1 1 (fun _ => 1) = 1 := by
  have h := traceExponentialCoefficient_eq_charpoly
    (p := 3) (1 : Matrix (Fin 1) (Fin 1) (ZMod 3)) (by decide) 1 (fun _ => 1)
    (by intro k _ _; simp)
  simpa [Matrix.charpoly_one, AddMonoidAlgebra.one_def, ZMod.val_one_eq_one_mod] using h

-- One fixed machine handles every binary coefficient address, including the zero default.
example : (fun d : ℕ => traceExponentialCoefficient 3 1 d (fun _ => 1)) ∈
    CountingFunction 5 encNat encNat := by
  simpa using (traceExponentialCoefficient_mem (a := 0) Decoder.nat
    (p := fun _ : ℕ => 3) (D := fun _ => 1) (d := fun d => d) (t := fun _ => 1)
    (ComputableInPolyTime.const 3) (ComputableInPolyTime.const 1) (by fun_prop)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1)))

-- At fixed parameters the relative polynomial specializes even over the integers.
open MvPolynomial.CriticalSystem in
example (u x : ℤ) :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := MvPolynomial.X (.inl 0) + MvPolynomial.X (.inr 0)
    let hF : F.totalDegree ≤ 2 := (MvPolynomial.totalDegree_add _ _).trans (by simp)
    (relativeValuePolynomial (by decide : 1 ≤ 2) F hF).map
      (MvPolynomial.eval₂Hom (Int.castRingHom ℤ)
        (fun i : Option (Fin 1) => i.elim u (fun _ => x))) =
    valuePolynomial (by decide : 1 ≤ 2) (fun _ => 0) u
      (MvPolynomial.X (0 : Fin 1) + MvPolynomial.C x)
      ((MvPolynomial.totalDegree_add _ _).trans (by
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
        decide)) := by
  intro F hF
  simpa [F] using relativeValuePolynomial_map (by decide : 1 ≤ 2) F hF u (fun _ => x)

-- A parameter variable remains in the constant coefficient of the witness polynomial.
open MvPolynomial in
open MvPolynomial.CriticalSystem in
example :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := X (.inr 0)
    ((relativeSource F).coeff 0).totalDegree = 1 ∧
      ((sumRingEquiv ℤ (Fin 1) (Option (Fin 1))).symm (relativeSource F)).coeffNorm1 ≤ 1 := by
  intro F
  refine ⟨?_, ?_⟩
  · simp [F, relativeSource]
  · simpa [F] using coeffNorm1_relativeSource_le F

-- One witness variable and one retained parameter give a parameter degree bound of two.
open MvPolynomial in
open MvPolynomial.CriticalSystem in
example :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := X (.inl 0) + X (.inr 0)
    ((criticalLower 2 (fun _ => 0) (X none) (relativeSource F) 0).coeff 0).totalDegree ≤ 2 ∧
      ((deformedPolynomial 2 (fun _ => 0) (X none)
        (relativeSource F)).coeff 0).totalDegree ≤ 2 := by
  intro F
  have hF : F.totalDegree ≤ 1 := (totalDegree_add _ _).trans (by simp)
  exact ⟨(totalDegree_coeff_relativeCriticalLower_le (by decide) F 0 0).trans
      (Nat.add_le_add_right hF 1),
    (totalDegree_coeff_relativeDeformedPolynomial_le 2 F 0).trans (Nat.add_le_add_right hF 1)⟩

-- Scaling a retained parameter records its degree and keeps it in the coefficient ring.
open MvPolynomial in
open MvPolynomial.CriticalSystem in
example :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := X (.inr 0)
    let p := (relativeSource F).coeff 0
    let scaled := MvPolynomial.aeval
      (fun i => (Polynomial.X : Polynomial (MvPolynomial (Option (Fin 1)) ℤ)) *
        Polynomial.C (X i)) p
    scaled.coeff 1 = X (some 0) ∧ scaled.natDegree = 1 := by
  intro F p scaled
  have hp : p = X (some 0) := by simp [p, F, relativeSource]
  dsimp only [scaled]
  constructor
  · rw [coeff_aeval_scale_X, hp]
    exact homogeneousComponent_eq_self (isHomogeneous_X ℤ (some 0))
  · rw [natDegree_aeval_scale_X, hp, totalDegree_X]

-- At the quotient dimension the reversed index vanishes, so the top coefficient
-- has degree zero even when the source contains a retained parameter.
open MvPolynomial in
open MvPolynomial.CriticalSystem in
example :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := X (.inl 0) + X (.inr 0)
    let hF : F.totalDegree ≤ 2 := (totalDegree_add _ _).trans (by simp)
    ((relativeValuePolynomial (by decide : 1 ≤ 2) F hF).coeff 2).totalDegree = 0 := by
  intro F hF
  apply Nat.eq_zero_of_le_zero
  simpa using totalDegree_relativeValuePolynomial_coeff_le (ell := 2) (by decide) F hF 2

-- The lower relation and objective retain their norm bounds with both blocks present.
open MvPolynomial in
open MvPolynomial.CriticalSystem in
example :
    let F : MvPolynomial (Fin 1 ⊕ Fin 1) ℤ := X (.inl 0) + X (.inr 0)
    let e := sumRingEquiv ℤ (Fin 1) (Option (Fin 1))
    (e.symm (criticalLower 2 (fun _ => 0) (X none) (relativeSource F) 0)).coeffNorm1 ≤ 2 ∧
      (e.symm (deformedPolynomial 2 (fun _ => 0) (X none) (relativeSource F))).coeffNorm1 ≤ 7 := by
  intro F e
  have hdegree : F.totalDegree ≤ 1 := (totalDegree_add _ _).trans (by simp)
  have hnorm : F.coeffNorm1 ≤ 2 := (MvPolynomial.coeffNorm1_add_le _ _).trans (by simp)
  refine ⟨(coeffNorm1_relativeCriticalLower_le (ell := 2) (by decide) F 0).trans ?_,
    (coeffNorm1_relativeDeformedPolynomial_le (ell := 2) (by decide) F).trans ?_⟩
  · exact Nat.mul_le_mul hdegree hnorm
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 hnorm) 1

end CslibFrontierTests.RealAlgebraicCharacteristic
