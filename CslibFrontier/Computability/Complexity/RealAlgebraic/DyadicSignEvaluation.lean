/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
public import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.MultiplicativeEnumeration

/-!
# Modular evaluation of the dyadic sign product

The factors in the dyadic sign product have short binary addresses. Their prime-field
product adds three counting levels, and the final modular power preserves that level.
Adding and subtracting the positive and reflected evaluations gives the cleared
denominator and numerator used by the integer sign-label score.

Adapted from `RationalSignEvaluation` and `SignTestEvaluation` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183` for the common-scale factors of
`Polynomial.dyadicSignProduct`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM

/-- Evaluate the dyadic product with padded binary addresses and a shared power of two. -/
@[expose] noncomputable def dyadicSignProductResidue (p B s z : ℕ) : ℕ :=
  let scale := powMod p 2 B
  let product := primeFieldProduct p (2 * B + 1).size fun w =>
    let j := BitString.binaryValue w
    if j < 2 * B + 1 then (powMod p 2 j + scale * z) % p else 1
  powMod p product (2 * s)

/-- For a uniformly accessible test value at level `F_a`, binary width and precision
give a dyadic sign product at level `F_(a+3)`. -/
theorem dyadicSignProductResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s z : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hz : z ∈ CountingFunction a enc encNat) :
    (fun w => dyadicSignProductResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encBits
  have hp' := hp.comp hf
  have hcount := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (.const 2) hB) (.const 1)
  have hj : ComputableInPolyTime (fun q : α × List Bool => BitString.binaryValue q.2)
      (encPair enc encBits) encNat := by fun_prop
  have hscale := computableInPolyTime_powMod hp (.const 2) hB
  have hweight := computableInPolyTime_powMod hp' (.const 2) hj
  have hscaled := CountingFunction.nat_mul (CountingFunction.of_polyTime (hscale.comp hf))
    (CountingFunction.preprocess hz hf)
  have hsum := CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hweight) hscaled)
    ComputableInPolyTime.binary_add
  have htest := CountingFunction.nat_lt (a := a) (CountingFunction.of_polyTime hj)
    (CountingFunction.of_polyTime (hcount.comp hf))
  have hfactor := CountingFunction.ite htest
    (CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp'))
    (CountingFunction.of_polyTime (.const 1))
  have hproduct := CountingFunction.primeFieldProduct_mem E hfactor hp
    (ComputableInPolyTime.binary_size.comp hcount)
  simpa only [dyadicSignProductResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.powMod (CountingFunction.of_polyTime hp) hproduct
      (CountingFunction.of_polyTime (ComputableInPolyTime.binary_mul' (.const 2) hs))

/-- The binary evaluator computes the common-scale integer polynomial at every prime. -/
theorem dyadicSignProductResidue_cast {p : ℕ} [Fact p.Prime] (B s z : ℕ) :
    (dyadicSignProductResidue p B s z : ZMod p) =
      (Polynomial.dyadicSignProduct B s).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  rw [dyadicSignProductResidue, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, primeFieldProduct_spec, Polynomial.eval₂_dyadicSignProduct]
  simp only [Nat.cast_ite, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [BitString.prod_binaryValue_lt (Nat.lt_size_self (2 * B + 1)).le
    (fun j => (2 : ZMod p) ^ j + 2 ^ B * z)]

/-- Sum of the two reflected product evaluations, used as the cleared denominator. -/
@[expose] noncomputable def signTestDenominatorResidue (p B s z : ℕ) : ℕ :=
  (dyadicSignProductResidue p B s z +
    dyadicSignProductResidue p B s (modularSub p 0 z)) % p

/-- Difference of the two reflected product evaluations, used as the cleared numerator. -/
@[expose] noncomputable def signTestNumeratorResidue (p B s z : ℕ) : ℕ :=
  modularSub p (dyadicSignProductResidue p B s z)
    (dyadicSignProductResidue p B s (modularSub p 0 z))

/-- The two cleared values preserve the common counting level of the dyadic products. -/
theorem signTestResidues_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s z : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hz : z ∈ CountingFunction a enc encNat) :
    ((fun w => signTestDenominatorResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat) ∧
    ((fun w => signTestNumeratorResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat) := by
  have hneg := modularSub_mem (CountingFunction.of_polyTime hp)
    (CountingFunction.of_polyTime (.const 0)) hz
  have hposProduct := dyadicSignProductResidue_mem E hp hB hs hz
  have hnegProduct := dyadicSignProductResidue_mem E hp hB hs hneg
  exact ⟨CountingFunction.nat_mod
    (CountingFunction.map (CountingFunction.prod hposProduct hnegProduct)
      ComputableInPolyTime.binary_add) (CountingFunction.of_polyTime hp),
    modularSub_mem (CountingFunction.of_polyTime hp) hposProduct hnegProduct⟩

/-- The cleared residues cast to the sum and difference used by the sign-label polynomial. -/
theorem signTestResidues_cast {p : ℕ} [Fact p.Prime] (B s z : ℕ) :
    let f := (Polynomial.dyadicSignProduct B s).eval₂ (Int.castRingHom (ZMod p))
    (signTestDenominatorResidue p B s z : ZMod p) = f (z : ZMod p) + f (-(z : ZMod p)) ∧
    (signTestNumeratorResidue p B s z : ZMod p) = f (z : ZMod p) - f (-(z : ZMod p)) := by
  have hp := (Fact.out : p.Prime).pos
  dsimp only
  constructor
  · rw [signTestDenominatorResidue, ZMod.natCast_mod, Nat.cast_add,
      dyadicSignProductResidue_cast, dyadicSignProductResidue_cast, modularSub_cast hp,
      Nat.cast_zero, zero_sub]
  · rw [signTestNumeratorResidue, modularSub_cast hp, dyadicSignProductResidue_cast,
      dyadicSignProductResidue_cast, modularSub_cast hp, Nat.cast_zero, zero_sub]

end Cslib.Complexity.RealAlgebraic
