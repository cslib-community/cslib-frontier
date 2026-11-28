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
# Characteristic coefficients of zero-centered critical systems

The zero-centered critical equations are `X i ^ ell + C u * pderiv i F = 0`.
Multiplication by a coordinate or by the deformed objective in their quotient has a
characteristic polynomial whose coefficients can be queried from modular evaluations of `F`.
`zeroObjectiveCoefficientValue` queries the objective coefficients, with a counting bound
in `zeroObjectiveCoefficientValue_mem` and prime-field correctness in
`zeroObjectiveCoefficientValue_eq`.

This adapts `LeanCanny.CountingHierarchy.zeroCoordinateCoefficientValue` at
lean-canny `970f28a5ecefc1327402ade16c068aa4b1b2c183`, the modular specialization
of the coordinate construction in [OpenAI2026CountingHierarchy], Proposition 6.3,
equation (6.11).
Selecting a deformation coefficient and proving coordinate coverage remain open.
The objective coefficients adapt `LeanCanny.CountingHierarchy.ZeroCenterAccess` and
`ZeroCenterCoefficientCorrectness` at the same commit. Evaluating the whole relative
characteristic polynomial remains open under
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem
  MvPolynomial.PurePower

private noncomputable def zeroCenteredCharacteristicValue (p n d u B k : ℕ)
    (multiplier value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  quotientCharacteristicValue p n ell B k multiplier
    (fun z => criticalJacobianValue p n ell u z value)
    (fun j z => modularSub p 0 (u * firstPartialResidue p n j z value))

private theorem zeroCenteredCharacteristicValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u B k : α → ℕ} {multiplier value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hB : ComputableInPolyTime B enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hmul : multiplier ∈ CountingFunction (a + 1) (encInstancePoint enc) encNat)
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => zeroCenteredCharacteristicValue (p w) (n w) (d w) (u w) (B w) (k w)
      (fun z => multiplier (w, z)) (fun y => value (w, y))) ∈
        CountingFunction (a + 9) enc encNat := by
  let Epoint := encList encNat
  let Eindexed := encPair encNat Epoint
  have hell := binary_add' hd (.const 1)
  have hf := fst enc Epoint
  have hz := snd enc Epoint
  have hpoint := fst (encPair enc Epoint) Epoint
  have hsource := CountingFunction.preprocess hv ((hf.comp hpoint).prod (snd _ _))
  have hJ := criticalJacobianValue_mem (Decoder.pair E (Decoder.list Decoder.nat))
    (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf) hz hsource
  have hf' := fst enc Eindexed
  have hj := (fst encNat Epoint).comp (snd enc Eindexed)
  have hz' := (snd encNat Epoint).comp (snd enc Eindexed)
  have hquery := fst (encPair enc Eindexed) Epoint
  have hsource' := CountingFunction.preprocess hv ((hf'.comp hquery).prod (snd _ _))
  have hpartial := firstPartialResidue_mem
    (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
    (hp.comp hf') (hn.comp hf') hj hz' hsource'
  have hlow := modularSub_mem (CountingFunction.of_polyTime (hp.comp hf'))
    (CountingFunction.of_polyTime (.const 0))
    (CountingFunction.nat_mul (CountingFunction.of_polyTime (hu.comp hf')) hpartial)
  simpa only [zeroCenteredCharacteristicValue, Function.comp_apply, Nat.add_assoc] using
    quotientCharacteristicValue_mem E hp hn hell hB hk hmul hJ hlow

private theorem zeroCenteredCharacteristicValue_eq {p n B : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (u k : ℕ) (F v : MvPolynomial (Fin n) (ZMod p))
    (hF : F.totalDegree ≤ d + 1)
    {b : ℕ} (hb : 1 ≤ b) (hvdeg : v.totalDegree ≤ b)
    (hB : (d + 1) ^ n * b + n * d ≤ B) (hcut : (d + 1) * (B + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (multiplier value : List ℕ → ℕ)
    (hmul : ∀ z, (multiplier z : ZMod p) = eval
      (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hv : ∀ z, (value z : ZMod p) = eval
      (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    zeroCenteredCharacteristicValue p n d u B k multiplier value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ F hF) v).charpoly.coeff k).val := by
  let r := criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F
  have hr (j : Fin n) : (r j).totalDegree ≤ d :=
    Nat.le_of_lt_succ (criticalLower_degree (d + 1) (by omega) _ _ F hF j)
  have hdim : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have hbpos : 1 ≤ (d + 1) ^ n * b := Nat.mul_le_mul hdim hb
  have hsize : (d + 1) * 2 ≤ (d + 1) * (B + 1) := Nat.mul_le_mul_left _ (by omega)
  have hp : 3 < p := by omega
  have hsmall : F.totalDegree < p - 1 := by omega
  unfold zeroCenteredCharacteristicValue
  refine quotientCharacteristicValue_eq d hd r hr v ?_ hcut hdegree _ _ _
    (fun _ _ => hmul _) ?_ ?_
  · intro m _ hm
    calc
      _ ≤ (v ^ m).totalDegree + (jacobian (d + 1) r).totalDegree := totalDegree_mul _ _
      _ ≤ (d + 1) ^ n * b + n * d := Nat.add_le_add
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul hm hvdeg))
        (totalDegree_jacobian_le d r hr)
      _ ≤ B := hB
  · intro _ _
    exact criticalJacobianValue_cast F (fun _ => 0) (d + 1) u _ value hsmall hp hv
  · intro j _ _
    rw [modularSub_cast (Fact.out : p.Prime).pos, Nat.cast_zero, Nat.cast_mul,
      firstPartialResidue_cast F j _ value hsmall (by omega) hv]
    simp only [r, criticalLower, zero_pow (by omega : d + 1 ≠ 0), map_sub, map_mul, eval_C]

/-- An addressed characteristic coefficient for coordinate multiplication in the
zero-centered quotient at deformation parameter `u`. Point lists are zero-padded. -/
noncomputable def criticalCoordinateCoefficientValue (p n d u i k : ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  zeroCenteredCharacteristicValue p n d u ((d + 1) ^ n + n * d) k
    (fun z => z[i]?.getD 0 % p) value

/-- The arity is unary, and the modulus, degree parameter, deformation parameter,
coordinate index and coefficient index are binary. Source evaluation at level `a`
gives a coordinate characteristic coefficient query at level `a + 9`. -/
theorem criticalCoordinateCoefficientValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u i k : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => criticalCoordinateCoefficientValue (p w) (n w) (d w) (u w) (i w) (k w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 9) enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hB := binary_add' (binary_pow' hell hn) (binary_mul' (unary_to_binary.comp hn) hd)
  have hf := fst enc (encList encNat)
  have hz := snd enc (encList encNat)
  have hread : ComputableInPolyTime (fun (w, z) => z[i w]?.getD 0)
      (encInstancePoint enc) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      listGetD_binary 0 hz (hi.comp hf)
  have hcoordinate := CountingFunction.of_polyTime (a := a + 1)
    (binary_mod.comp (hread.prod (hp.comp hf)))
  have hcoeff := zeroCenteredCharacteristicValue_mem E hp hn hd hu hB hk hcoordinate hv
  simpa only [criticalCoordinateCoefficientValue, Function.comp_apply] using hcoeff

/-- The queried residue is the corresponding characteristic coefficient of multiplication
by `X i` in the actual pure-power quotient over the prime field. -/
theorem criticalCoordinateCoefficientValue_eq {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (u k : ℕ) (i : Fin n) (F : MvPolynomial (Fin n) (ZMod p))
    (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ z, (value z : ZMod p) = eval
      (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    criticalCoordinateCoefficientValue p n d u i.val k value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ F hF) (X i)).charpoly.coeff k).val :=
  zeroCenteredCharacteristicValue_eq d hd u k F (X i) hF (b := 1) le_rfl
    (totalDegree_X_le i) (by simpa only [mul_one] using Nat.le_refl ((d + 1) ^ n + n * d))
    hcut hdegree _ value
    (fun _ => by simp only [ZMod.natCast_mod, eval_X]) hv

/-- An addressed characteristic coefficient for multiplication by the zero-centered deformed
objective at parameter `u`. The point lists supplied to `value` use zero padding. -/
noncomputable def zeroObjectiveCoefficientValue (p n d u k : ℕ) (value : List ℕ → ℕ) : ℕ :=
  zeroCenteredCharacteristicValue p n d u ((d + 1) ^ n * (d + 2) + n * d) k
    (fun z => zeroObjectiveValue p n (d + 1) u z value) value

/-- Uniform source evaluation at level `a` gives objective coefficients at level `a + 9`.
The arity is unary. The modulus, degree parameter, deformation and address are binary. -/
theorem zeroObjectiveCoefficientValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u k : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hv : value ∈ CountingFunction a (encInstancePoint enc) encNat) :
    (fun w => zeroObjectiveCoefficientValue (p w) (n w) (d w) (u w) (k w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 9) enc encNat := by
  have hell := binary_add' hd (.const 1)
  have hB := binary_add' (binary_mul' (binary_pow' hell hn) (binary_add' hd (.const 2)))
    (binary_mul' (unary_to_binary.comp hn) hd)
  have hf := fst enc (encList encNat)
  have hz := snd enc (encList encNat)
  have hsource := CountingFunction.preprocess hv ((hf.comp (fst (encInstancePoint enc) _)).prod
    (snd _ _))
  have hobj := zeroObjectiveValue_mem (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf)
    hz hsource
  have hcoeff := zeroCenteredCharacteristicValue_mem E hp hn hd hu hB hk
    (CountingFunction.mono (by omega : a ≤ a + 1) hobj) hv
  simpa only [zeroObjectiveCoefficientValue, Function.comp_apply] using hcoeff

/-- The objective coefficient query returns the residue of the actual zero-centered quotient
characteristic coefficient over the prime field, with the trace interpolation cutoffs. -/
theorem zeroObjectiveCoefficientValue_eq {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (u k : ℕ) (F : MvPolynomial (Fin n) (ZMod p))
    (hF : F.totalDegree ≤ d + 1)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ z, (value z : ZMod p) = eval
      (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    zeroObjectiveCoefficientValue p n d u k value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1)
        (criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ F hF)
        (deformedPolynomial (d + 1) (fun _ => 0) (u : ZMod p) F)).charpoly.coeff k).val :=
  zeroCenteredCharacteristicValue_eq d hd u k F _ hF (b := d + 2) (by omega)
    (totalDegree_deformedPolynomial_le (d + 1) _ _ F (hF.trans (by omega))) le_rfl
    hcut hdegree _ value (fun z => zeroObjectiveValue_cast F (d + 1) u (by omega) z value hv) hv

end Cslib.Complexity.RealAlgebraic
