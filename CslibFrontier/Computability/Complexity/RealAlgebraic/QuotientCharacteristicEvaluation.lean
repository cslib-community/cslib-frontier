/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
public import CslibFrontier.Computability.Complexity.RealAlgebraic.QuotientTraceEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CharacteristicCoefficients
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic coefficients and determinants of pure-power quotients

`quotientCharacteristicValue` composes the constructed modular power-trace evaluator with
trace-to-characteristic reconstruction. Uniform `F_a` evaluation access to the objective,
Jacobian, and relation polynomials gives an `F_(a+8)` coefficient evaluator. It builds neither
the quotient multiplication matrix nor a list of its exponentially many entries or traces.
The variable count is unary; the modulus, relation exponent, degree budget and requested
coefficient address are binary. Above the quotient dimension the total evaluator returns zero.

At a sufficiently large prime, canonical grid-point evaluations of those polynomials suffice
for correctness against the characteristic polynomial of the actual normal-monomial
multiplication matrix. The degree budget is needed only for positive powers through the
dimension. Coefficient specialization before evaluation gives the reduction of the source
characteristic coefficient over any commutative coefficient ring. The signed constant
coefficient gives the determinant at the same counting level.

Adapted from `LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation`,
`QuotientCharacteristicSpecialization`, and `QuotientDeterminantEvaluation` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, as a component of the real-counting development
tracked by [#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial MvPolynomial.PurePower

/-- The entire trace-to-characteristic computation uses only polynomial
 evaluations and short binary indices. -/
@[expose] noncomputable def quotientCharacteristicValue (p n ell B m : ℕ)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  traceExponentialCoefficient p (ell ^ n) m (fun k => quotientTraceValue p n ell B k v J r)

/-- Uniform polynomial evaluations in `F_a` give actual quotient
 characteristic coefficients in `F_(a+8)`, without a trace oracle. -/
theorem quotientCharacteristicValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B m : α → ℕ}
    {v J : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hm : ComputableInPolyTime m enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hJ : J ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => quotientCharacteristicValue (p w) (n w) (ell w) (B w) (m w)
      (fun z => v (w, z)) (fun z => J (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 8) enc encNat := by
  have hv' : (fun q : (α × ℕ) × List ℕ => v (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encList encNat)) encNat :=
    CountingFunction.preprocess hv (by fun_prop)
  have hJ' : (fun q : (α × ℕ) × List ℕ => J (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encList encNat)) encNat :=
    CountingFunction.preprocess hJ (by fun_prop)
  have hr' : (fun q : (α × ℕ) × (ℕ × List ℕ) => r (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encPair encNat (encList encNat))) encNat :=
    CountingFunction.preprocess hr (by fun_prop)
  have ht : (fun q : α × ℕ => quotientTraceValue (p q.1) (n q.1) (ell q.1) (B q.1) q.2
      (fun z => v (q.1, z)) (fun z => J (q.1, z)) (fun i z => r (q.1, i, z))) ∈
        CountingFunction (a + 5) (encPair enc encNat) encNat := by
    simpa only [Function.comp_apply] using
      quotientTraceValue_mem (Decoder.pair E Decoder.nat)
        (hp.comp (.fst enc encNat)) (hn.comp (.fst enc encNat))
        (hell.comp (.fst enc encNat)) (hB.comp (.fst enc encNat)) (.snd enc encNat) hv' hJ' hr'
  simpa only [quotientCharacteristicValue] using CountingFunction.mono (b := a + 8) (by omega)
    (traceExponentialCoefficient_mem (a := a + 5) E hp
      (ComputableInPolyTime.binary_pow' hell hn) hm ht)

/-- Compute the characteristic coefficient of the actual normal-basis multiplication matrix.
Only positive powers need numerator-degree and trace correctness bounds; the zero trace slot
is ignored. The single dimension cutoff also guarantees the denominator inverses. -/
theorem quotientCharacteristicValue_eq {p n B m : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (ZMod p)) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (ZMod p))
    (hdeg : ∀ k, 1 ≤ k → k ≤ (d + 1) ^ n →
      (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        (jacobian (d + 1) r))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) (r i)) :
    quotientCharacteristicValue p n (d + 1) B m value Jvalue rvalue =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff m).val := by
  have hdim : Fintype.card (NormalIndex n (d + 1)) = (d + 1) ^ n := by simp [NormalIndex]
  simpa only [quotientCharacteristicValue, hdim] using traceExponentialCoefficient_eq_charpoly
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v)
    (by simpa only [hdim] using hdegree) m
    (fun k => quotientTraceValue p n (d + 1) B k value Jvalue rvalue) fun k hk hle =>
      quotientTraceValue_cast d hd r hr v (hdeg k hk (by simpa only [hdim] using hle))
        hcut value Jvalue rvalue hvalue hJvalue hrvalue

/-- Evaluating the specialized polynomials gives the source matrix's characteristic coefficient
reduced by `φ`. The coefficient ring may itself be a polynomial ring in deformation parameters.
The same cutoff and uniform evaluator apply even when `φ` is noninjective. -/
theorem quotientCharacteristicValue_eq_specialization
    {S : Type*} [CommRing S] {p n B m : ℕ} [Fact p.Prime] (φ : S →+* ZMod p)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hdeg : ∀ k, 1 ≤ k → k ≤ (d + 1) ^ n →
      (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) (v.map φ))
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        ((jacobian (d + 1) r).map φ))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) ((r i).map φ)) :
    quotientCharacteristicValue p n (d + 1) B m value Jvalue rvalue =
      (φ ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff m)).val := by
  have h := quotientCharacteristicValue_eq (m := m) d hd _
    (fun i => (totalDegree_map_le φ (r i)).trans (hr i)) (v.map φ)
    (fun k hk hK => by
      rw [← jacobian_map, ← map_pow, ← map_mul]
      exact (totalDegree_map_le φ _).trans (hdeg k hk hK))
    hcut hdegree value Jvalue rvalue hvalue (by simpa only [jacobian_map] using hJvalue) hrvalue
  rwa [← multiplicationMatrix_map φ (by omega) r
    (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v, Matrix.charpoly_map,
    Polynomial.coeff_map] at h

/-- Evaluate the integer-residue determinant by signing the constant characteristic coefficient. -/
@[expose] noncomputable def quotientDeterminantValue (p n ell B : ℕ)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  (powMod p (modularSub p 0 1) (ell ^ n) *
    quotientCharacteristicValue p n ell B 0 v J r) % p

/-- The sign correction preserves the counting level of the characteristic-coefficient
evaluator. -/
theorem quotientDeterminantValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B : α → ℕ}
    {v J : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hJ : J ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => quotientDeterminantValue (p w) (n w) (ell w) (B w)
      (fun z => v (w, z)) (fun z => J (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 8) enc encNat := by
  exact CountingFunction.nat_mod
    (CountingFunction.nat_mul (CountingFunction.of_polyTime
      (computableInPolyTime_powMod hp (modularSub_polyTime hp (.const 0) (.const 1))
        (.binary_pow' hell hn)))
      (quotientCharacteristicValue_mem E hp hn hell hB (.const 0) hv hJ hr))
    (CountingFunction.of_polyTime hp)

/-- At a prime satisfying the quotient coefficient cutoffs, specialized polynomial evaluation
recovers the image of the original multiplication determinant. -/
theorem quotientDeterminantValue_cast
    {S : Type*} [CommRing S] {p n B : ℕ} [Fact p.Prime] (φ : S →+* ZMod p)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hdeg : ∀ k, 1 ≤ k → k ≤ (d + 1) ^ n →
      (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) (v.map φ))
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        ((jacobian (d + 1) r).map φ))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) ((r i).map φ)) :
    (quotientDeterminantValue p n (d + 1) B value Jvalue rvalue : ZMod p) =
      φ (multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).det := by
  have hdim : Fintype.card (NormalIndex n (d + 1)) = (d + 1) ^ n := by simp [NormalIndex]
  have hp : p.Prime := Fact.out
  rw [quotientDeterminantValue, ZMod.natCast_mod, Nat.cast_mul,
    powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    modularSub_cast hp.pos, Nat.cast_zero, Nat.cast_one, zero_sub,
    quotientCharacteristicValue_eq_specialization φ d hd r hr v hdeg hcut hdegree
      value Jvalue rvalue hvalue hJvalue hrvalue, ZMod.natCast_zmod_val,
    Matrix.det_eq_sign_charpoly_coeff, map_mul, map_pow, map_neg, map_one, hdim]

end Cslib.Complexity.RealAlgebraic
