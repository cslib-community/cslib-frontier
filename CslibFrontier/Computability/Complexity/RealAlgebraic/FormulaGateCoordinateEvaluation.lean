/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.UnaryModularList
public import CslibFrontier.Computability.Complexity.RealAlgebraic.FormulaGateCoefficientEvaluation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder

/-!
# Indexed coordinate evaluation at Kronecker points

An indexed evaluator for individual bivariate coordinates supplies the list needed
by the formula gate evaluator. The query uses the two values `z` and `z ^ radix`
in the same order as the variables of the substituted polynomial. The second
value is computed by modular powering. The list length is the raw formula word
length, so collecting the residues preserves the evaluator's counting-function level.

This combines the indexed coordinate queries in
`LeanCanny.ETR.BivariateTermReader.coordinates` at lean-canny
`970f28a5ecefc1327402ade16c068aa4b1b2c183` with Frontier's modular list builder.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Logic.RealArithmetic Turing.MultiTapeTM ComputableInPolyTime

/-- Evaluate one coordinate at a bivariate point over the supplied modulus. -/
structure FormulaGateCoordinateQuery (α : Type) where
  /-- The input instance used by the coordinate family. -/
  context : α
  /-- The modulus of the coordinate query. -/
  modulus : ℕ
  /-- The value of the inner variable. -/
  innerValue : ℕ
  /-- The value of the outer variable. -/
  outerValue : ℕ
  /-- The index of the requested coordinate. -/
  index : ℕ

variable {α : Type}

/-- The context, modulus, inner value and outer value are framed in order, followed by
the coordinate index. All four numbers use binary encoding. -/
enc_structure encFormulaGateCoordinateQuery (enc : α ↪ List Bool) :
    FormulaGateCoordinateQuery α where
  context : enc, modulus : encNat, innerValue : encNat, outerValue : encNat, index : encNat

/-- Read the coordinate residues at a Kronecker point in variable order. The zero modulus
uses modulus one, which gives a list of zeros. -/
@[expose] def formulaWordGateKroneckerCoordinates (word : List Bool) (context : α)
    (p z inner : ℕ) (value : FormulaGateCoordinateQuery α → ℕ) : List ℕ :=
  let modulus := max p 1
  let radix := formulaWordGateKroneckerRadix word inner
  unaryModularList word.length modulus fun k =>
    value ⟨context, modulus, z % modulus, powMod modulus z radix, k⟩

/-- Collecting coordinate values at a Kronecker point preserves their counting-function
level. The query is a context paired with a binary modulus, then paired with a binary
field representative. -/
theorem formulaWordGateKroneckerCoordinates_mem {enc : α ↪ List Bool} {a : ℕ}
    {word : α → List Bool} {inner : α → ℕ} {value : FormulaGateCoordinateQuery α → ℕ}
    (hword : ComputableInPolyTime word enc encBits)
    (hinner : ComputableInPolyTime inner enc encNat)
    (hvalue : value ∈ CountingFunction a (encFormulaGateCoordinateQuery enc) encNat) :
    (fun ((w, p), z) => formulaWordGateKroneckerCoordinates (word w) w p z (inner w) value) ∈
      CountingFunction a (encPair (encPair enc encNat) encNat) (encList encNat) := by
  let packedQuery := encPair (encPair enc encNat) encNat
  have hcontext := (fst enc encNat).comp (fst (encPair enc encNat) encNat)
  have hp := (snd enc encNat).comp (fst (encPair enc encNat) encNat)
  have hz := snd (encPair enc encNat) encNat
  have hmod := binary_max' hp (.const 1)
  have hradix := formulaWordGateKroneckerRadix_polyTime (hword.comp hcontext)
    (hinner.comp hcontext)
  have hx := binary_mod.comp (hz.prod hmod)
  have hy := computableInPolyTime_powMod hmod hz hradix
  have hq := fst packedQuery encNat
  have hscalar := CountingFunction.preprocess hvalue (encFormulaGateCoordinateQuery_mk_polyTime enc
    (hcontext.comp hq) (hmod.comp hq) (hx.comp hq) (hy.comp hq) (snd packedQuery encNat))
  have hn := length_bits.comp (hword.comp hcontext)
  exact unaryModularList_mem hn hmod (fun _ => (le_max_right _ _ : 1 ≤ _)) hscalar

/-- If a scalar query agrees with bivariate evaluation on canonical field representatives,
the collected list gives the specialized coordinate at each variable of the formula word. -/
theorem formulaWordGateKroneckerCoordinates_get_cast (word : List Bool) (context : α)
    {p : ℕ} (hp : 0 < p) (z inner : ℕ) (hz : z < p)
    (coordinates : Fin word.length → Polynomial (Polynomial ℤ))
    (value : FormulaGateCoordinateQuery α → ℕ)
    (hvalue : ∀ x y : ℕ, x < p → y < p → ∀ k : Fin word.length,
      (value ⟨context, p, x, y, k.val⟩ : ZMod p) =
        Polynomial.aevalAeval (x : ZMod p) (y : ZMod p) (coordinates k))
    (k : Fin word.length) :
    (((formulaWordGateKroneckerCoordinates word context p z inner value)[k.val]?.getD 0 : ℕ) :
      ZMod p) = Polynomial.aevalAeval (z : ZMod p)
        ((z : ZMod p) ^ formulaWordGateKroneckerRadix word inner) (coordinates k) := by
  let radix := formulaWordGateKroneckerRadix word inner
  have hy : powMod p z radix < p := by
    rw [powMod_of_ne_zero hp.ne']
    exact Nat.mod_lt _ hp
  rw [formulaWordGateKroneckerCoordinates, max_eq_left hp,
    unaryModularList_get _ _ _ k.isLt, ZMod.natCast_mod, Nat.mod_eq_of_lt hz,
    hvalue _ _ hz hy k, powMod_of_ne_zero hp.ne', ZMod.natCast_mod, Nat.cast_pow]

end Cslib.Complexity.RealAlgebraic
