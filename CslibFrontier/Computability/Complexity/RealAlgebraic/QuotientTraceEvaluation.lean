/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ResidueEvaluation
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.MultiplicationMatrix

/-!
# Uniform modular power traces of pure-power quotients

Compute the trace of the actual normal-basis multiplication matrix by evaluating the finite
residue of `v^k` times the Jacobian. The algorithm uses only uniform modular evaluations of
`v`, the Jacobian and the relations; it constructs neither the quotient matrix nor its powers.
Its correctness follows from the constructed residue evaluator and the algebraic trace
identity, including multiple roots. The counting-function certificate costs five levels.

This is the generic trace-evaluation step from
`LeanCanny.CountingHierarchy.QuotientTraceEvaluation` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. Constructing critical-system and Jacobian evaluation
from a controlled input polynomial, and completing the real-counting endpoints, remain
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial MvPolynomial.PurePower

/-- Compute a power trace by the finite residue of `v^k J`.
 The Jacobian is evaluated as a polynomial, without a quotient matrix. -/
@[expose] noncomputable def quotientTraceValue (p n ell B k : ℕ)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  residueValue p n ell B (fun z => (powMod p (v z) k * J z) % p) r

theorem quotientTraceValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B k : α → ℕ}
    {v J : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hJ : J ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => quotientTraceValue (p w) (n w) (ell w) (B w) (k w)
      (fun z => v (w, z)) (fun z => J (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 5) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc (encList encNat))
  have hk' := hk.comp (ComputableInPolyTime.fst enc (encList encNat))
  have hnum := CountingFunction.nat_mod
    (CountingFunction.nat_mul (CountingFunction.powMod (CountingFunction.of_polyTime hp') hv
      (CountingFunction.of_polyTime hk')) hJ) (CountingFunction.of_polyTime hp')
  simpa only [quotientTraceValue, Function.comp_apply] using
    residueValue_mem E hp hn hell hB hnum hr

/-- The trace evaluator is correct for the actual normal-basis matrix, including repeated
roots. Its prime cutoff ensures Fourier non-aliasing, so these primes exceed `d + 1`. -/
theorem quotientTraceValue_cast {p n B k : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (ZMod p)) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (ZMod p))
    (hdeg : (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        (jacobian (d + 1) r))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) (r i)) :
    (quotientTraceValue p n (d + 1) B k value Jvalue rvalue : ZMod p) =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ k).trace := by
  rw [quotientTraceValue, multiplicationMatrix_trace_pow d hd r hr v k]
  apply residueValue_cast (by omega) r _ _ hdeg hcut _ rvalue _ hrvalue
  · intro i
    exact (hr i).trans_lt (Nat.lt_succ_self d)
  · intro s hs
    rw [ZMod.natCast_mod, Nat.cast_mul, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
      ZMod.natCast_mod, Nat.cast_pow, hvalue s hs, hJvalue s hs, map_mul, map_pow]

end Cslib.Complexity.RealAlgebraic
