/-
Copyright (c) 2026 lean-canny contributors and Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.OfFn
public import CslibFrontier.Computability.Complexity.RealAlgebraic.CoefficientEvaluation
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Factorial
public import CslibFrontier.Foundations.Data.Polynomial.FiniteExponential

/-!
# Modular coefficients of a finite exponential

Uniform coefficients in `F_a` give polynomial evaluation in `F_(a+1)`, finite-exponential
evaluation in `F_(max (a+1) 3 + 1)`, and its addressed coefficients in
`F_(max (a+1) 3 + 2)`. The degree, modulus and coefficient address are binary
polynomial-time functions. Summation and product certificates include all query,
intermediate and output lengths, without expanding the coefficient vector or factorials.

Correctness at a prime requires `D < p` for the factorial denominators and
`D * D < p - 1` for extraction without aliasing. The mathematical polynomial is
`Polynomial.finiteExponential D (Polynomial.ofFn (D + 1) c)`.

Adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/TraceExponential.lean).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM Polynomial
open scoped BigOperators

/-- Modular evaluation of a polynomial from its uniform coefficient residues. -/
@[expose] noncomputable def coefficientPolynomialResidue (p D z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range (D + 1), c k * powMod p z k) % p

/-- Modular evaluation of the truncated exponential, using only short indices. -/
@[expose] noncomputable def truncatedExponentialResidue (p D z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ j ∈ Finset.range (D + 1),
    powMod p (factorialResidue p j) (p - 2) *
      powMod p (coefficientPolynomialResidue p D z c) j) % p

/-- Coefficient reconstruction is one more uniform Fourier sum. -/
@[expose] noncomputable def truncatedExponentialCoefficient (p D k : ℕ) (c : ℕ → ℕ) : ℕ :=
  coefficientResidue p k (fun z => truncatedExponentialResidue p D z c)

theorem coefficientPolynomialResidue_cast {p : ℕ} [Fact p.Prime] (D z : ℕ) (c : ℕ → ℕ) :
    (coefficientPolynomialResidue p D z c : ZMod p) =
      (ofFn (D + 1) (fun k => (c k : ZMod p))).eval (z : ZMod p) := by
  rw [ofFn_eq_sum_monomial]
  simp only [coefficientPolynomialResidue, ZMod.natCast_mod, Nat.cast_sum,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Nat.cast_mul,
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    Finset.sum_range]

theorem truncatedExponentialResidue_cast {p : ℕ} [Fact p.Prime] {D : ℕ}
    (hD : D < p) (z : ℕ) (c : ℕ → ℕ) :
    (truncatedExponentialResidue p D z c : ZMod p) =
      (finiteExponential D (ofFn (D + 1) (fun k => (c k : ZMod p)))).eval (z : ZMod p) := by
  simp only [truncatedExponentialResidue, ZMod.natCast_mod, Nat.cast_sum,
    finiteExponential, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [factorialResidue_inverse (by have := Finset.mem_range.mp hj; omega),
    powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod,
    Nat.cast_pow, coefficientPolynomialResidue_cast]

/-- Correct canonical coefficients of the actual truncated-exponential polynomial. -/
theorem truncatedExponentialCoefficient_eq {p : ℕ} [Fact p.Prime] {D k : ℕ}
    (hdegree : D * D < p - 1) (hk : k < p - 1) (c : ℕ → ℕ) :
    truncatedExponentialCoefficient p D k c =
      ((finiteExponential D (ofFn (D + 1) (fun i => (c i : ZMod p)))).coeff k).val := by
  apply coefficientResidue_eq_val
    (finiteExponential D (ofFn (D + 1) (fun i => (c i : ZMod p)))) k
    (fun z => truncatedExponentialResidue p D z c)
    ((natDegree_finiteExponential_le D _).trans_lt
      ((Nat.mul_le_mul_left D (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _))).trans_lt
        hdegree)) hk
  intro z _
  exact truncatedExponentialResidue_cast
    (by have := (Nat.le_mul_self D).trans_lt hdegree; omega) z c

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- One sum evaluates a coefficient-specified polynomial with binary degree bound. -/
theorem coefficientPolynomialResidue_mem (E : Decoder enc) {p D z : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => coefficientPolynomialResidue (p w) (D w) (z w) (fun k => c (w, k))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hz' := hz.comp (ComputableInPolyTime.fst enc encNat)
  have hpower := CountingFunction.powMod (a := a) (CountingFunction.of_polyTime hp')
    (CountingFunction.of_polyTime hz')
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd enc encNat))
  exact CountingFunction.nat_mod
    (CountingFunction.sum_range E (CountingFunction.nat_mul hc hpower)
      (ComputableInPolyTime.binary_add' hD (.const 1)))
    (CountingFunction.of_polyTime hp)

/-- The factorial and inner-sum oracles combine at one fixed maximum level. -/
theorem truncatedExponentialResidue_mem (E : Decoder enc) {p D z : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => truncatedExponentialResidue (p w) (D w) (z w) (fun k => c (w, k))) ∈
      CountingFunction (max (a + 1) 3 + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hs := coefficientPolynomialResidue_mem E hp hD hz hc
  have hs' := CountingFunction.preprocess (input := encPair enc encNat) hs
    (g := fun q : α × ℕ => q.1) (ComputableInPolyTime.fst enc encNat)
  have hfac := CountingFunction.preprocess (input := encPair enc encNat) factorialResidue_mem
    (g := fun q : α × ℕ => (p q.1, q.2)) (hp'.prod (ComputableInPolyTime.snd _ _))
  have hinv := CountingFunction.powMod (a := max (a + 1) 3)
    (CountingFunction.of_polyTime hp') (CountingFunction.mono (Nat.le_max_right _ _) hfac)
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_sub' hp' (.const 2)))
  have hpower := CountingFunction.powMod (a := max (a + 1) 3)
    (CountingFunction.of_polyTime hp') (CountingFunction.mono (Nat.le_max_left _ _) hs')
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd enc encNat))
  exact CountingFunction.nat_mod
    (CountingFunction.sum_range E (CountingFunction.nat_mul hinv hpower)
      (ComputableInPolyTime.binary_add' hD (.const 1)))
    (CountingFunction.of_polyTime hp)

/-- Indexed truncated-exponential coefficients are available at fixed depth.
This certificate constructs the sums and modular denominators rather than
assuming an exponential-sized matrix or coefficient oracle. -/
theorem truncatedExponentialCoefficient_mem (E : Decoder enc) {p D k : α → ℕ}
    {c : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => truncatedExponentialCoefficient (p w) (D w) (k w) (fun i => c (w, i))) ∈
      CountingFunction (max (a + 1) 3 + 2) enc encNat := by
  have hc' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) encNat) hc
    (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  -- Specify evaluator arguments so inference does not unfold their aggregation sums.
  have heval :=
    truncatedExponentialResidue_mem (a := a) (enc := encPair enc encNat)
      (p := fun q => p q.1) (D := fun q => D q.1) (z := fun q => q.2)
      (c := fun q => c (q.1.1, q.2)) (Decoder.pair E Decoder.nat)
      (hp.comp (ComputableInPolyTime.fst enc encNat))
      (hD.comp (ComputableInPolyTime.fst enc encNat))
      (ComputableInPolyTime.snd enc encNat) hc'
  exact coefficientResidue_mem (a := max (a + 1) 3 + 1) (p := p) (k := k)
    (value := fun q => truncatedExponentialResidue (p q.1) (D q.1) q.2
      (fun i => c (q.1, i))) E hp hk heval

end Cslib.Complexity.RealAlgebraic
