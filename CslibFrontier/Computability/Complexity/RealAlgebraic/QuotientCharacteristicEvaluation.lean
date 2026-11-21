/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.QuotientTraceEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CharacteristicCoefficients

/-!
# Characteristic coefficients of pure-power quotients from polynomial evaluations

`quotientCharacteristicValue` composes the constructed modular power-trace evaluator with
trace-to-characteristic reconstruction. Uniform `F_a` evaluation access to the objective,
Jacobian, and relation polynomials gives an `F_(a+8)` coefficient evaluator. It builds neither
the quotient multiplication matrix nor a list of its exponentially many entries or traces.
The variable count is unary; the modulus, relation exponent, degree budget and requested
coefficient address are binary. Above the quotient dimension the total evaluator returns zero.

At a sufficiently large prime, canonical grid-point evaluations of those polynomials suffice
for correctness against the characteristic polynomial of the actual normal-monomial
multiplication matrix. The degree budget is needed only for positive powers through the
dimension. This generic component assumes polynomial evaluation access; constructing that
access for controlled critical systems and completing real-truth bounds are separate steps.

Ported from `LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation` at lean-canny commit
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
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hn' := hn.comp (ComputableInPolyTime.fst enc encNat)
  have hell' := hell.comp (ComputableInPolyTime.fst enc encNat)
  have hB' := hB.comp (ComputableInPolyTime.fst enc encNat)
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
      quotientTraceValue_mem (Decoder.pair E Decoder.nat) hp' hn' hell' hB'
        (ComputableInPolyTime.snd enc encNat) hv' hJ' hr'
  have hc := traceExponentialCoefficient_mem (a := a + 5) E hp
    (ComputableInPolyTime.binary_pow' hell hn) hm ht
  simpa only [quotientCharacteristicValue] using
    CountingFunction.mono (b := a + 8) (by omega) hc

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
  have hdim : Fintype.card (NormalIndex n (d + 1)) = (d + 1) ^ n := by
    simp [NormalIndex]
  have h := traceExponentialCoefficient_eq_charpoly
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v)
    (by simpa only [hdim] using hdegree) m
    (fun k => quotientTraceValue p n (d + 1) B k value Jvalue rvalue) (by
      intro k hk hle
      exact quotientTraceValue_cast d hd r hr v (hdeg k hk (by simpa only [hdim] using hle))
        hcut value Jvalue rvalue hvalue hJvalue hrvalue)
  simpa only [quotientCharacteristicValue, hdim] using h

end Cslib.Complexity.RealAlgebraic
