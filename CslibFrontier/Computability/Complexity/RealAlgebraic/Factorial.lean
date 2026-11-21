/-
Copyright (c) 2026 lean-canny contributors and Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorial.NatCast
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-!
# Factorials modulo a prime from binary indices

`factorialResidue` computes a factorial modulo the supplied modulus without constructing
that factorial. The binary index gives a polynomial-size enumeration width, and the existing
uniform prime-field product evaluator supplies an `F_3` certificate. Algebraic correctness
and inversion hold at primes, with invertibility restricted to indices below the prime.

Adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/Factorial.lean).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-- A binary-width product with one outside the factorial range. -/
@[expose] noncomputable def factorialResidue (p j : ℕ) : ℕ :=
  primeFieldProduct p j.size (fun w =>
    if BitString.binaryValue w < j then BitString.binaryValue w + 1 else 1)

/-- The argument's binary size bounds the enumeration width; no factorial
or exponentially long list is passed to the realizing machine. -/
theorem factorialResidue_mem :
    (fun q : ℕ × ℕ => factorialResidue q.1 q.2) ∈
      CountingFunction 3 (encPair encNat encNat) encNat := by
  have hf : (fun q : (ℕ × ℕ) × List Bool =>
      if BitString.binaryValue q.2 < q.1.2 then BitString.binaryValue q.2 + 1 else 1) ∈
        CountingFunction 0 (encPair (encPair encNat encNat) encBits) encNat := by
    apply CountingFunction.of_polyTime
    have htest : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × List Bool => decide (BitString.binaryValue q.2 < q.1.2))
        (encPair (encPair encNat encNat) encBits) encBool := by fun_prop
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (by fun_prop) (ComputableInPolyTime.const 1)
  exact CountingFunction.primeFieldProduct_mem (Decoder.pair Decoder.nat Decoder.nat) hf
    (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.snd _ _))

/-- The total evaluator is the true factorial residue at every prime. -/
theorem factorialResidue_cast {p : ℕ} [Fact p.Prime] (j : ℕ) :
    (factorialResidue p j : ZMod p) = (j.factorial : ZMod p) := by
  rw [factorialResidue, primeFieldProduct_spec, Nat.factorial_eq_prod_range_add_one,
    Nat.cast_prod]
  simp only [Nat.cast_ite, Nat.cast_one]
  have h := BitString.sum_binaryValue_lt (M := Additive (ZMod p)) (Nat.lt_size_self j).le
    (fun i => Additive.ofMul ((i + 1 : ℕ) : ZMod p))
  exact congrArg Additive.toMul h

/-- Factorials below the prime are invertible, including zero factorial. -/
theorem factorialResidue_ne_zero {p : ℕ} [Fact p.Prime] {j : ℕ} (hj : j < p) :
    (factorialResidue p j : ZMod p) ≠ 0 := by
  rw [factorialResidue_cast]
  exact isUnit_iff_ne_zero.mp ((IsUnit.natCast_factorial_iff_of_charP p).mpr hj)

/-- Modular powering supplies the inverse denominator without integer division
by the potentially enormous factorial. -/
theorem factorialResidue_inverse {p : ℕ} [Fact p.Prime] {j : ℕ} (hj : j < p) :
    (powMod p (factorialResidue p j) (p - 2) : ZMod p) =
      (j.factorial : ZMod p)⁻¹ := by
  rw [powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod,
    Nat.cast_pow, ZMod.pow_card_sub_two_eq_inv (factorialResidue_ne_zero hj),
    factorialResidue_cast]

end Cslib.Complexity.RealAlgebraic
