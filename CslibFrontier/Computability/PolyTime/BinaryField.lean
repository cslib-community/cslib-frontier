/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldTable
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Data.List.GetD

/-!
# Polynomial-time binary-field operations

Trial division and exhaustive irreducible-polynomial search are polynomial in the **unary
search bound**, not in the degree. Coordinate multiplication is polynomial uniformly in its
table. These certificates are shared by affine dispersers, hardness encodings and small-bias
spaces; logarithmic degrees make the search polynomial in the latter constructions' parameters.

## Main results

* `Cslib.BinaryField.computableInPolyTime_leastIrreducibleCode`: bounded modulus search.
* `Cslib.BinaryField.computableInPolyTime_fieldMul`: coordinate multiplication.
-/

@[expose] public section

namespace Cslib.BinaryField

open Turing.MultiTapeTM ComputableInPolyTime

attribute [local irreducible] ComputableInPolyTime

/-! ### Binary polynomials -/

/-- Multiplication by `X` modulo a binary polynomial, on coefficient lists. -/
@[fun_prop]
theorem computableInPolyTime_mulXMod :
    ComputableInPolyTime (fun p : List Bool × List Bool => mulXMod p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold mulXMod
  fun_prop

private theorem length_mulXMod_le (g r : List Bool) : (mulXMod g r).length ≤ g.length - 1 :=
  List.length_take_le _ _

/-- The remainder modulo a binary polynomial, by a left fold over the coefficients whose state, the
current power of `X` and the partial remainder, never exceeds the degree of the modulus. -/
@[fun_prop]
theorem computableInPolyTime_modBits :
    ComputableInPolyTime (fun p : List Bool × List Bool => modBits p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hstep : ComputableInPolyTime
      (fun q : (List Bool × (List Bool × List Bool)) × Bool => modStep q.1.1 q.1.2 q.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    unfold modStep
    fun_prop
  have hinit : ComputableInPolyTime (fun p : List Bool × List Bool =>
      ((true :: List.replicate (p.1.length - 2) false).take (p.1.length - 1),
        List.replicate (p.1.length - 1) false))
      (encPair encBits encBits) (encPair encBits encBits) := by
    fun_prop
  have h := (foldlWith_spec (encA := encBool) (encL := encBits) (par := Prod.fst)
    (list := Prod.snd) (step := modStep) (fst encBits encBits) (snd encBits encBits) hinit hstep
    (fun p _ state => state.1.length ≤ p.1.length - 1 ∧ state.2.length ≤ p.1.length - 1)
    (fun p => by simp) (fun p consumed state value _ h => by
      refine ⟨length_mulXMod_le _ _, ?_⟩
      simp only [modStep]
      split_ifs
      · simp only [List.length_zipWith]
        omega
      · exact h.2)
    (size := fun p => 3 * p.1.length + 1) (.of_forall_le 3 1 fun p => by simp; omega)
    (fun p consumed state _ h => by simp [encPair_apply]; omega)).1
  exact (snd encBits encBits).comp h

/-- The binary digits of a unary natural. -/
theorem computableInPolyTime_bits_unary :
    ComputableInPolyTime Nat.bits encUnary encBits :=
  (of_eq (f := Nat.bits) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp
    unary_to_binary

/-- The irreducibility test by trial division, on a unary code. -/
@[fun_prop]
theorem computableInPolyTime_isIrreducibleCode :
    ComputableInPolyTime isIrreducibleCode encUnary encBool := by
  unfold isIrreducibleCode divisorPasses
  have := computableInPolyTime_bits_unary
  fun_prop

/-- The exhaustive search for the least irreducible code below a unary bound. -/
@[fun_prop]
theorem computableInPolyTime_leastIrreducibleCode :
    ComputableInPolyTime (fun q : ℕ × ℕ => leastIrreducibleCode q.1 q.2)
      (encPair encUnary encUnary) encUnary := by
  unfold leastIrreducibleCode
  fun_prop

/-- The remainders of the powers of `X`. -/
@[fun_prop]
theorem computableInPolyTime_powerTable :
    ComputableInPolyTime powerTable encBits (encList encBits) := by
  unfold powerTable
  fun_prop


/-- A multiplication table, as a list of rows of coordinate words. -/
abbrev encTable : List (List (List Bool)) ↪ List Bool :=
  encList (encList encBits)

/-- An entry of a computed multiplication table. -/
@[fun_prop]
theorem computableInPolyTime_tableEntry {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {u w : α → ℕ}
    (htab : ComputableInPolyTime tab input encTable)
    (hu : ComputableInPolyTime u input encUnary)
    (hw : ComputableInPolyTime w input encUnary) :
    ComputableInPolyTime (fun a => tableEntry (tab a) (u a) (w a)) input encBits :=
  ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.listGetDWithInput htab hu []) hw []

/-- **Multiplication in coordinates**, uniformly in the multiplication table: the sum of at most
`n ^ 2` table entries, `n` the number of rows. -/
theorem computableInPolyTime_fieldMul : ComputableInPolyTime
    (fun p : List (List (List Bool)) × List Bool × List Bool => fieldMul p.1 p.2.1 p.2.2)
    (encPair encTable (encPair encBits encBits)) encBits := by
  unfold fieldMul
  fun_prop

/-- Multiplication in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableInPolyTime_fieldMul' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {a b : α → List Bool}
    (htab : ComputableInPolyTime tab input encTable)
    (ha : ComputableInPolyTime a input encBits)
    (hb : ComputableInPolyTime b input encBits) :
    ComputableInPolyTime (fun x => fieldMul (tab x) (a x) (b x)) input encBits := by
  simpa only [Function.comp_def] using computableInPolyTime_fieldMul.comp (htab.prod (ha.prod hb))

theorem length_fieldMul (tab : List (List (List Bool))) (a b : List Bool) :
    (fieldMul tab a b).length = tab.length := by
  simp [fieldMul]

/-- The multiplication table of the power basis, from the coefficient list of the modulus. -/
@[fun_prop]
theorem computableInPolyTime_powerMulTable :
    ComputableInPolyTime powerMulTable encBits encTable := by
  unfold powerMulTable
  fun_prop

/-- The traces of the basis elements can be extracted in polynomial time from the
coordinate multiplication table. -/
@[fun_prop]
theorem computableInPolyTime_traceVector {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))}
    (htab : ComputableInPolyTime tab input encTable) :
    ComputableInPolyTime (fun a => traceVector (tab a)) input encBits := by
  unfold traceVector
  fun_prop

/-- Construct the binary-field multiplication table when the number of field elements
is polynomially bounded in the encoded input length. -/
theorem computableInPolyTime_fieldTable {α : Type} {input : α ↪ List Bool} {k : α → ℕ}
    (hk : ComputableInPolyTime k input encUnary)
    (hsize : PolyBounded (fun a => (input a).length) (fun a => 2 ^ k a)) :
    ComputableInPolyTime (fun a => fieldTable (k a)) input encTable := by
  have hq : ComputableInPolyTime (fun a => 2 ^ k a) input encUnary := by
    simpa only [Function.comp_def, BitString.length_enumList] using
      (length_list encBits).comp (bitsEnumList_of_polyBounded hk hsize)
  have hbound : ComputableInPolyTime (fun a => 2 ^ (k a + 1)) input encUnary := by
    simpa only [pow_succ, Function.comp_def] using unary_mul.comp (hq.prod (const 2))
  have hmod := computableInPolyTime_bits_unary.comp
    (computableInPolyTime_leastIrreducibleCode.comp (hbound.prod hk))
  simpa only [fieldTable, modulusBits, Function.comp_def] using
    computableInPolyTime_powerMulTable.comp hmod

end Cslib.BinaryField

namespace Cslib.BitString

open Cslib.BinaryField Turing.MultiTapeTM ComputableInPolyTime

/-- Coordinate powering is polynomial-time in the unary exponent, input word and table. -/
theorem powerWord_polyTime {α : Type} {encIn : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {x : α → List Bool} {i : α → ℕ}
    (htab : ComputableInPolyTime tab encIn encTable)
    (hx : ComputableInPolyTime x encIn encBits)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun a => powerWord (tab a) (x a) (i a)) encIn encBits := by
  unfold powerWord
  refine iterateWithInput_of_bounded_growth hi (const [true]) ?_
    ⟨((length_list (encList encBits)).comp htab).polyBounded, fun a z => ?_⟩
  · exact computableInPolyTime_fieldMul' (htab.comp (fst _ _)) (snd _ _)
      (hx.comp (fst _ _))
  · simp [length_fieldMul]

end Cslib.BitString
