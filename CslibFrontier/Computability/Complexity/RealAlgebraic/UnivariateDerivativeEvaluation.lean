/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Factorial
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Modular evaluation of binary-order univariate derivatives

One bounded counting sum visits addressed coefficients. The algorithm takes the degree bound
and derivative order in binary and uses modular descending factorials for the derivative weights.

Adapted from `DerivativeEvaluation` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183` for the sparse root-label tests.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Turing.MultiTapeTM
open scoped BigOperators

/-- The evaluation residue obtained from the addressed coefficients of the original polynomial. -/
@[expose] noncomputable def univariateDerivativeResidue (p D k z : ℕ) (c : ℕ → ℕ) : ℕ :=
  (∑ j ∈ Finset.range (D + 1), if j + k ≤ D then
    c (j + k) * descFactorialResidue p (j + k) k * powMod p z j else 0) % p

/-- Uniform coefficient access in `F_a` yields derivative evaluation at level
`F_(max a 3 + 1)`. -/
theorem univariateDerivativeResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D k z : α → ℕ} {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => univariateDerivativeResidue (p w) (D w) (k w) (z w) (fun i => c (w, i))) ∈
      CountingFunction (max a 3 + 1) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hj := ComputableInPolyTime.snd enc encNat
  have hjk := ComputableInPolyTime.binary_add' hj (hk.comp hf)
  have hcoeff := CountingFunction.preprocess hc (hf.prod hjk)
  have hfall := descFactorialResidue_mem (hp.comp hf) hjk (hk.comp hf)
  have hpower := computableInPolyTime_powMod (hp.comp hf) (hz.comp hf) hj
  have hvalue := CountingFunction.nat_mul
    (CountingFunction.nat_mul (CountingFunction.mono (Nat.le_max_left _ _) hcoeff)
      (CountingFunction.mono (Nat.le_max_right _ _) hfall)) (CountingFunction.of_polyTime hpower)
  have htest : ComputableInPolyTime
      (fun q : α × ℕ => decide (q.2 + k q.1 ≤ D q.1)) (encPair enc encNat) encBool := by
    fun_prop
  have hterm := CountingFunction.ite (CountingFunction.of_polyTime htest) hvalue
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))
  have hsum := CountingFunction.sum_range E hterm
    (ComputableInPolyTime.binary_add' hD (.const 1))
  simpa only [univariateDerivativeResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

/-- Correctness includes orders beyond the degree of the polynomial. Only addressed
coefficients up to the supplied degree bound need to be correct. -/
theorem univariateDerivativeResidue_cast {p D k z : ℕ} [Fact p.Prime]
    (q : Polynomial (ZMod p)) (hq : q.natDegree ≤ D) (hD : D < p)
    (c : ℕ → ℕ) (hc : ∀ i ≤ D, (c i : ZMod p) = q.coeff i) :
    (univariateDerivativeResidue p D k z c : ZMod p) =
      (Polynomial.derivative^[k] q).eval (z : ZMod p) := by
  have hdegree : (Polynomial.derivative^[k] q).natDegree < D + 1 :=
    (Polynomial.natDegree_iterate_derivative q k).trans_lt (by omega)
  conv_rhs => rw [(Polynomial.derivative^[k] q).as_sum_range' (D + 1) hdegree]
  rw [univariateDerivativeResidue, ZMod.natCast_mod, Nat.cast_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_monomial, Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  by_cases hjk : j + k ≤ D
  · rw [ite_eq_left hjk, Nat.cast_mul, Nat.cast_mul, hc (j + k) hjk,
      descFactorialResidue_cast (hjk.trans_lt hD),
      powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow]
    ring
  · rw [ite_eq_right hjk, Nat.cast_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < j + k)]
    simp

end Cslib.Complexity.RealAlgebraic
