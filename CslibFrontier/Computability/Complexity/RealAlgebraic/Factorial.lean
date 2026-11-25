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
Taking a factorial ratio gives descending factorial residues at the same counting level.

Adapted from
[lean-canny's factorial evaluator](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/Factorial.lean)
and `FallingFactorial` at the same revision.
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

/-- A descending factorial modulo the supplied modulus, returning zero above its index. -/
@[expose] noncomputable def descFactorialResidue (p i k : ℕ) : ℕ :=
  if k ≤ i then
    (factorialResidue p i * powMod p (factorialResidue p (i - k)) (p - 2)) % p
  else 0

/-- Both factorials and the modular inverse are computed at the same counting level. -/
theorem descFactorialResidue_mem {α : Type} {enc : α ↪ List Bool}
    {p i k : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hk : ComputableInPolyTime k enc encNat) :
    (fun w => descFactorialResidue (p w) (i w) (k w)) ∈ CountingFunction 3 enc encNat := by
  have hnum := CountingFunction.preprocess factorialResidue_mem (hp.prod hi)
  have hden := CountingFunction.preprocess factorialResidue_mem
    (hp.prod (ComputableInPolyTime.binary_sub' hi hk))
  have hinv := CountingFunction.powMod (CountingFunction.of_polyTime hp) hden
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_sub' hp (.const 2)))
  have hval := CountingFunction.nat_mod (CountingFunction.nat_mul hnum hinv)
    (CountingFunction.of_polyTime hp)
  have htest : ComputableInPolyTime (fun w => decide (k w ≤ i w)) enc encBool := by fun_prop
  simpa only [descFactorialResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime htest) hval
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))

/-- Below the prime, the evaluator agrees with the descending factorial for every order. -/
theorem descFactorialResidue_cast {p i k : ℕ} [Fact p.Prime] (hi : i < p) :
    (descFactorialResidue p i k : ZMod p) = (i.descFactorial k : ZMod p) := by
  by_cases hk : k ≤ i
  · have hlt := (Nat.sub_le i k).trans_lt hi
    rw [descFactorialResidue, ite_eq_left hk, ZMod.natCast_mod, Nat.cast_mul,
      factorialResidue_cast, factorialResidue_inverse hlt]
    have hfac : ((i - k).factorial : ZMod p) ≠ 0 := by
      rw [← factorialResidue_cast]
      exact factorialResidue_ne_zero hlt
    have heq := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.factorial_mul_descFactorial hk)
    simp only [Nat.cast_mul] at heq
    rw [← heq]
    field_simp
  · simp only [descFactorialResidue, ite_eq_right hk,
      Nat.descFactorial_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero]

end Cslib.Complexity.RealAlgebraic
