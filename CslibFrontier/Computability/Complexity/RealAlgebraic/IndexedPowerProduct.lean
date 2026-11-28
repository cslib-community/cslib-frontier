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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

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
  primeFieldRangeProduct p n (fun i => powMod p (value i) (j[i]?.getD 0))

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
  have hfst := ComputableInPolyTime.fst enc encNat
  have hsnd := ComputableInPolyTime.snd enc encNat
  have he : ComputableInPolyTime
      (fun q : α × ℕ => (j q.1)[q.2]?.getD 0) (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hj.comp hfst) hsnd
  exact CountingFunction.primeFieldRangeProduct_mem E hp hn
    (CountingFunction.powMod (CountingFunction.of_polyTime (hp.comp hfst)) hv
      (CountingFunction.of_polyTime he))

/-- Padded binary addresses enumerate precisely the genuine factors, including an empty product.
Missing list entries have exponent zero; correctness imposes no list-length assumption. -/
theorem indexedPowerProduct_cast {p : ℕ} [Fact p.Prime] (n : ℕ) (j : List ℕ)
    (value : ℕ → ℕ) :
    (indexedPowerProduct p n j value : ZMod p) =
      ∏ i : Fin n, (value i.val : ZMod p) ^ (j[i.val]?.getD 0) := by
  rw [indexedPowerProduct, primeFieldRangeProduct_cast]
  simp only [powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, ZMod.natCast_mod, Nat.cast_pow]

end Cslib.Complexity.RealAlgebraic
