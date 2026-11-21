/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Products
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.MultiplicativeEnumeration
import Mathlib.Algebra.BigOperators.Fin

/-!
# Uniform indexed products of modular powers

`indexedPowerProduct p n j value` multiplies `value i` raised to its list-addressed exponent
for `i < n`, using short binary addresses. Addresses at or above `n` contribute one, and missing
exponents default to zero. The evaluator uses modular powering and the total prime-field
product construction; it does not form unreduced powers or their full product.

`indexedPowerProduct_mem` proves the `F_(a+3)` bound for uniformly accessible `F_a` bases.
The modulus, arity and exponent list use binary natural encodings; the address width is the
unary bit-length of the arity. `indexedPowerProduct_cast` identifies the actual prime-field
product. At nonprime moduli the underlying product evaluator has its total zero default.

Ported from `LeanCanny.CountingHierarchy.IndexedPowerProduct` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, as a step toward uniform residue and trace evaluation.
The product bound reuses the existing counting-hierarchy products API.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM
open scoped BigOperators

/-- Exponents are addressed in a short list. The total product evaluator
 pads the binary index domain with factors equal to one. -/
@[expose] noncomputable def indexedPowerProduct (p n : ℕ) (j : List ℕ)
    (value : ℕ → ℕ) : ℕ :=
  primeFieldProduct p n.size (fun w =>
    if BitString.binaryValue w < n then
      powMod p (value (BitString.binaryValue w)) (j[BitString.binaryValue w]?.getD 0)
    else 1)

/-- Binary arity and binary power exponents cost three additional function levels.
Only the bit-length of the binary arity is supplied to the short-index product evaluator. -/
theorem indexedPowerProduct_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {j : α → List ℕ} {value : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encNat)
    (hj : ComputableInPolyTime j enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => indexedPowerProduct (p w) (n w) (j w) (fun i => value (w, i))) ∈
      CountingFunction (a + 3) enc encNat := by
  have hi : ComputableInPolyTime (fun q : α × List Bool => BitString.binaryValue q.2)
      (encPair enc encBits) encNat := by fun_prop
  have hp' := hp.comp (ComputableInPolyTime.fst enc encBits)
  have hn' := hn.comp (ComputableInPolyTime.fst enc encBits)
  have hj' := hj.comp (ComputableInPolyTime.fst enc encBits)
  have he : ComputableInPolyTime
      (fun q : α × List Bool => (j q.1)[BitString.binaryValue q.2]?.getD 0)
      (encPair enc encBits) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hj' hi
  have hvalue := CountingFunction.preprocess hv
    ((ComputableInPolyTime.fst enc encBits).prod hi)
  have hpower := CountingFunction.powMod (CountingFunction.of_polyTime hp') hvalue
    (CountingFunction.of_polyTime he)
  have htest := CountingFunction.nat_lt (a := a) (CountingFunction.of_polyTime hi)
    (CountingFunction.of_polyTime hn')
  have hfactor := CountingFunction.ite htest hpower
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
  simpa only [indexedPowerProduct, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.primeFieldProduct_mem E hfactor hp (ComputableInPolyTime.binary_size.comp hn)

/-- Padded binary addresses enumerate precisely the genuine factors, including an empty product.
Missing list entries have exponent zero; correctness imposes no list-length assumption. -/
theorem indexedPowerProduct_cast {p : ℕ} [Fact p.Prime] (n : ℕ) (j : List ℕ)
    (value : ℕ → ℕ) :
    (indexedPowerProduct p n j value : ZMod p) =
      ∏ i : Fin n, (value i.val : ZMod p) ^ (j[i.val]?.getD 0) := by
  rw [indexedPowerProduct, primeFieldProduct_spec]
  simp only [Nat.cast_ite, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one]
  rw [BitString.prod_binaryValue_lt (Nat.lt_size_self n).le
    (fun i => (value i : ZMod p) ^ (j[i]?.getD 0)), Finset.prod_range]

end Cslib.Complexity.RealAlgebraic
