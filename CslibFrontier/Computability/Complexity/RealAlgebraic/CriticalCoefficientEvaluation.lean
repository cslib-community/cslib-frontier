/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CriticalJacobianEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.QuotientCharacteristicEvaluation

/-!
# Characteristic coefficients of parameterized critical systems

Construct addressed characteristic coefficients of the actual critical quotient from uniform
input evaluation at a cost of nine counting-function levels. The deformation parameter `u`
is explicit; the relations and Jacobian are constructed from the input evaluator.

Adapted from `LeanCanny.CountingHierarchy.CriticalEvaluationAccess` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. Canonical parameter selection, specialization
bounds and real feasibility remain [#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial MvPolynomial.CriticalSystem
  MvPolynomial.PurePower

/-- All three access programs are constructed from the same source evaluator.
The Jacobian and lower relations require only one additional function level. -/
private theorem criticalEvaluationAccess_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell u : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    ((fun q : α × List ℕ => criticalObjectiveValue (p q.1) (n q.1) (ell q.1) (u q.1)
      q.2 (fun y => value (q.1, y))) ∈ CountingFunction a (encPair enc (encList encNat)) encNat) ∧
    ((fun q : α × List ℕ => criticalJacobianValue (p q.1) (n q.1) (ell q.1) (u q.1)
      q.2 (fun y => value (q.1, y))) ∈
      CountingFunction (a + 1) (encPair enc (encList encNat)) encNat) ∧
    ((fun q : α × (ℕ × List ℕ) => criticalLowerValue (p q.1) (n q.1) (ell q.1) (u q.1)
      q.2.1 q.2.2 (fun y => value (q.1, y))) ∈
        CountingFunction (a + 1) (encPair enc (encPair encNat (encList encNat))) encNat) := by
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hz := ComputableInPolyTime.snd enc (encList encNat)
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc (encList encNat)) (encList encNat)) hv
    (g := fun q : (α × List ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hobj := criticalObjectiveValue_mem (hp.comp hf) (hn.comp hf)
    (hell.comp hf) (hu.comp hf) hz hv'
  have hJ := criticalJacobianValue_mem (Decoder.pair E (Decoder.list Decoder.nat))
    (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf) hz hv'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hobj
  · simpa only [Function.comp_apply] using hJ
  · have hf₂ := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    have hi : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1)
        (encPair enc (encPair encNat (encList encNat))) encNat := by fun_prop
    have hz₂ : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2)
        (encPair enc (encPair encNat (encList encNat))) (encList encNat) := by fun_prop
    have hv₂ := CountingFunction.preprocess
      (input := encPair (encPair enc (encPair encNat (encList encNat))) (encList encNat)) hv
      (g := fun q : (α × (ℕ × List ℕ)) × List ℕ => (q.1.1, q.2)) (by fun_prop)
    simpa only [Function.comp_apply] using criticalLowerValue_mem
      (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
      (hp.comp hf₂) (hn.comp hf₂) (hell.comp hf₂) (hu.comp hf₂) hi hz₂ hv₂

/-- An addressed characteristic coefficient of the critical system with deformation `u`. -/
@[expose] noncomputable def criticalCoefficientValue (p n d u m : ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  quotientCharacteristicValue p n ell (ell ^ n * (d + 2) + n * d) m
    (fun z => criticalObjectiveValue p n ell u z value)
    (fun z => criticalJacobianValue p n ell u z value)
    (fun i z => criticalLowerValue p n ell u i z value)

/-- Uniform input evaluation in `F_a` gives parameterized critical coefficients in `F_(a+9)`.
The variable count is unary; the modulus, degree, parameter and address are binary. -/
theorem criticalCoefficientValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u m : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hm : ComputableInPolyTime m enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalCoefficientValue (p w) (n w) (d w) (u w) (m w)
      (fun y => value (w, y))) ∈
      CountingFunction (a + 9) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have haccess := criticalEvaluationAccess_mem E hp hn hell hu hv
  have hdim := ComputableInPolyTime.binary_pow' hell hn
  have hB := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' hdim (ComputableInPolyTime.binary_add' hd (.const 2)))
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.unary_to_binary.comp hn) hd)
  have hcoeff := quotientCharacteristicValue_mem E hp hn hell hB hm
    (CountingFunction.mono (by omega : a ≤ a + 1) haccess.1) haccess.2.1 haccess.2.2
  simpa only [criticalCoefficientValue, Nat.add_assoc, Function.comp_apply] using hcoeff

/-- Correctness for the actual parameterized critical quotient. The cutoff uses short
bounds; no relation, Jacobian, matrix or characteristic-polynomial oracle is assumed. -/
theorem criticalCoefficientValue_eq {p n m : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (u : ℕ) (F : MvPolynomial (Fin n) (ZMod p))
    (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) F) :
    criticalCoefficientValue p n d u m value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1)
          (fun i : Fin n => ((separatedCenters (d + 1) i : ℕ) : ZMod p)) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ F hF)
        (deformedPolynomial (d + 1)
          (fun i : Fin n => ((separatedCenters (d + 1) i : ℕ) : ZMod p))
          (u : ZMod p) F)).charpoly.coeff m).val := by
  let centers : Fin n → ZMod p := fun i => (separatedCenters (d + 1) i : ℕ)
  let r := criticalLower (d + 1) centers (u : ZMod p) F
  let v := deformedPolynomial (d + 1) centers (u : ZMod p) F
  have hr : ∀ i, (r i).totalDegree ≤ d := fun i =>
    Nat.le_of_lt_succ (criticalLower_degree (d + 1) (by omega) centers _ F hF i)
  have hvdeg : v.totalDegree ≤ d + 2 :=
    totalDegree_deformedPolynomial_le (d + 1) centers _ F (hF.trans (by omega))
  have hdim : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have hB : d + 2 ≤ (d + 1) ^ n * (d + 2) + n * d := by nlinarith
  have hp : 3 < p := by nlinarith
  have hcut' : (d + 1) ^ n * (d + 2) + n * d + 1 < p := by
    have hmul : (d + 1) ^ n * (d + 2) + n * d + 1 ≤
        (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hFp : F.totalDegree < p - 1 := by omega
  unfold criticalCoefficientValue
  refine quotientCharacteristicValue_eq d hd r hr v ?_ hcut hdegree
    _ _ _ ?_ ?_ ?_
  · intro k _ hk
    exact (totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_pow v k).trans (Nat.mul_le_mul hk hvdeg))
      (totalDegree_jacobian_le d r hr))
  · intro s _
    exact criticalObjectiveValue_cast F (d + 1) u _ value hv
  · intro s _
    exact criticalJacobianValue_cast F (d + 1) u _ value hFp hp hv
  · intro i s _
    exact criticalLowerValue_cast F (d + 1) u i _ value hFp (by omega) hv

end Cslib.Complexity.RealAlgebraic
