/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.LowBits
public import CslibFrontier.Foundations.FieldTheory.Finite.Basic
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryPolynomial
import CslibFrontier.Computability.Machines.Turing.MultiTape.InputAt
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Executable bytes for the degree-eight binary field

`Cslib.GF256.Byte` is the canonical little-endian polynomial-basis byte for
`F₂[X] / (X⁸ + X⁴ + X³ + X + 1)`.  Its operations are executable list algorithms:
addition is byte XOR and multiplication folds the existing `Cslib.modStep` reduction by the
source modulus `0x11b`.  Exponentiation is the little-endian square-and-multiply fold; inversion
is exponentiation by `254`, with `0⁻¹ = 0`, and division inherits that total convention.

The semantic theorems identify every operation with the existing `Cslib.BinaryField 8`.  The
native compiler section retains concrete finite-control transition tables rather than selecting
machines from finite-domain computability.  Binary-operation inputs are exactly the two raw
eight-bit words concatenated; their fixed widths make framing unnecessary.

## Main definitions

* `Cslib.GF256.Byte`, `.encoding`, `.pairEncoding`, `.powEncoding`: canonical raw encodings.
* `Cslib.GF256.add`, `.mul`, `.pow`, `.inv`, `.div`: executable field operations.
* `Cslib.GF256.equivBinaryField`: the existing power-basis equivalence with `BinaryField 8`.
* `Cslib.GF256.Native.binaryCompiler`: a constructive retained table for any binary byte
  operation, with exact static-size, time and workspace coordinates.
* `Cslib.GF256.Native.invCompiler`: the retained fixed-width inversion table.
* `Cslib.GF256.Native.powCompiler`: the retained streaming exponentiation table.

## Main results

* `Cslib.GF256.bits_ofBits`, `.ofBits_bits`: exact-width codec laws.
* `Cslib.GF256.field_add`, `.field_mul`, `.field_pow`, `.field_inv`, `.field_div`: semantic
  refinement to `BinaryField 8`.
* `Cslib.GF256.Native.computesTidily_binaryTable`: the retained table computes its operation in
  41 steps and zero workspace.
* `Cslib.GF256.Native.computesTidily_unaryTable`: fixed-width unary operations take 25 steps and
  zero workspace.
* `Cslib.GF256.Native.computesTidily_powTable`: exponentiation has clock
  `2 * inputLength + 10` and zero workspace.
* `Cslib.GF256.Native.invCompiler_resourceBounds`, `.powCompiler_resourceBounds`: checked tape,
  state, transition-row and whole-program bounds for the retained inversion and exponentiation
  compilers.
* `Cslib.GF256.Native.computableInPolyTime_binary`, `.computableInPolyTime_unary`, and
  `.computableInPolyTime_pow`: the corresponding asymptotic witnesses.
-/

public section

namespace Cslib.GF256

open BitString Polynomial

/-- A polynomial-basis byte, numbered by its eight coefficients least significant first. -/
abbrev Byte := Fin 256

/-- The eight little-endian coefficients of a byte. -/
@[expose] def bits (a : Byte) : List Bool := lowBits 8 a.val

@[simp]
theorem length_bits (a : Byte) : (bits a).length = 8 := by simp [bits]

/-- Read the first eight little-endian coefficients, padding a short word and truncating a long
word. -/
@[expose] def ofBits (word : List Bool) : Byte :=
  BitString.equivFin 8 (BitString.ofList 8 word)

/-- Encoding and then decoding a byte is exact. -/
@[simp]
theorem ofBits_bits (a : Byte) : ofBits (bits a) = a := by
  change BitString.equivFin 8 (BitString.ofList 8 (lowBits 8 a.val)) = a
  rw [lowBits_eq_ofFn_equivFin_symm, BitString.ofList_ofFn, Equiv.apply_symm_apply]

/-- Decoding and re-encoding an exact eight-bit word is exact. -/
theorem bits_ofBits {word : List Bool} (hword : word.length = 8) :
    bits (ofBits word) = word := by
  rw [bits, ofBits, lowBits_eq_ofFn_equivFin_symm, Equiv.symm_apply_apply]
  exact BitString.ofFn_ofList hword

/-- Canonical raw eight-bit encoding of a byte. -/
@[expose] def encoding : Byte ↪ List Bool where
  toFun := bits
  inj' a b h := by
    rw [← ofBits_bits a, ← ofBits_bits b, h]

/-- Two canonical bytes concatenated without a delimiter: bits `0…7` are the left operand and
bits `8…15` are the right operand. -/
def pairBits (input : Byte × Byte) : List Bool := bits input.1 ++ bits input.2

@[simp]
theorem length_pairBits (input : Byte × Byte) : (pairBits input).length = 16 := by
  simp [pairBits]

/-- Canonical raw sixteen-bit encoding of a pair of bytes. -/
@[expose] def pairEncoding : Byte × Byte ↪ List Bool where
  toFun := pairBits
  inj' left right h := by
    obtain ⟨hleft, hright⟩ := List.append_inj h (by simp)
    exact Prod.ext (encoding.injective hleft) (encoding.injective hright)

/-- A byte followed by a little-endian, unframed binary exponent.  The first eight bits are always
the base, so the variable-length suffix is unambiguous. -/
def powBits (input : Byte × ℕ) : List Bool := bits input.1 ++ input.2.bits

@[simp]
theorem length_powBits (input : Byte × ℕ) :
    (powBits input).length = 8 + input.2.bits.length := by
  simp [powBits]

/-- Canonical encoding of a byte and a natural exponent. -/
@[expose] def powEncoding : Byte × ℕ ↪ List Bool where
  toFun := powBits
  inj' left right h := by
    have hleft : bits left.1 = bits right.1 := by
      simpa [powBits] using congrArg (List.take 8) h
    have hright : left.2.bits = right.2.bits := by
      simpa [powBits] using congrArg (List.drop 8) h
    apply Prod.ext (encoding.injective hleft)
    simpa using congrArg lsbValue hright

/-- The lower eight coefficients of the source modulus `0x11b`. -/
@[expose] def modulusLow : List Bool := [true, true, false, true, true, false, false, false]

/-- Coefficients of `X⁸ + X⁴ + X³ + X + 1`, constant term first. -/
@[expose] def modulusBits : List Bool := modulusLow ++ [true]

@[simp]
theorem length_modulusLow : modulusLow.length = 8 := rfl

/-- Byte addition is coefficient-wise XOR. -/
@[expose] def add (input : Byte × Byte) : Byte :=
  ofBits (List.zipWith xor (bits input.1) (bits input.2))

/-- The byte representation of addition is exactly pointwise XOR. -/
theorem bits_add (input : Byte × Byte) :
    bits (add input) = List.zipWith xor (bits input.1) (bits input.2) := by
  apply bits_ofBits
  simp

/-- Byte multiplication: shift-and-reduce the first operand once for every coefficient of the
second, accumulating the selected powers by XOR. -/
@[expose] def mul (input : Byte × Byte) : Byte :=
  ofBits ((bits input.2).foldl (modStep modulusBits)
    (bits input.1, List.replicate 8 false)).2

private theorem length_mulWord (input : Byte × Byte) :
    ((bits input.2).foldl (modStep modulusBits)
      (bits input.1, List.replicate 8 false)).2.length = 8 := by
  have h := (length_foldl_modStep modulusLow (bits input.2) (bits input.1)
    (List.replicate 8 false) (by simp) (by simp)).2
  rw [length_modulusLow] at h
  simpa only [modulusBits] using h

/-- The byte representation of multiplication is the `modStep` remainder accumulator. -/
theorem bits_mul (input : Byte × Byte) :
    bits (mul input) =
      ((bits input.2).foldl (modStep modulusBits)
        (bits input.1, List.replicate 8 false)).2 := by
  exact bits_ofBits (length_mulWord input)

/-- One little-endian square-and-multiply round: square the current power and optionally multiply
it into the accumulator. -/
@[expose] def powStep (state : Byte × Byte) (bit : Bool) : Byte × Byte :=
  (mul (state.1, state.1), if bit then mul (state.2, state.1) else state.2)

/-- Exponentiation by the little-endian binary digits of the exponent. -/
@[expose] def pow (input : Byte × ℕ) : Byte :=
  (input.2.bits.foldl powStep (input.1, ⟨1, by norm_num⟩)).2

/-- Total inversion, with `inv 0 = 0`, by the finite-field exponent `254`. -/
@[expose] def inv (a : Byte) : Byte := pow (a, 254)

/-- Total division, with division by zero returning zero. -/
@[expose] def div (input : Byte × Byte) : Byte := mul (input.1, inv input.2)

/-! ### The source modulus and semantic field refinement -/

private theorem leastIrreducibleCode_eight : leastIrreducibleCode 512 8 = 283 := by
  have hlow :
      (List.range 256).find? (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by
    rw [List.find?_eq_none]
    intro m hm hpred
    have hm_lt : m < 256 := List.mem_range.mp hm
    have hlog : Nat.log 2 m ≠ 8 := by
      rcases eq_or_ne m 0 with rfl | hm0
      · norm_num
      · exact ne_of_lt (Nat.log_lt_of_lt_pow hm0 (by simpa using hm_lt))
    have hpred' : Nat.log 2 m = 8 ∧ isIrreducibleCode m = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using hpred
    exact hlog hpred'.1
  have h256 : (List.range' 256 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h260 : (List.range' 260 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h264 : (List.range' 264 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h268 : (List.range' 268 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h272 : (List.range' 272 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h276 : (List.range' 276 4).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h280 : (List.range' 280 1).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h281 : (List.range' 281 1).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h282 : (List.range' 282 1).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = none := by decide
  have h283_log : Nat.log 2 283 = 8 := by decide
  have h283_irreducible : isIrreducibleCode 283 = true := by
    unfold isIrreducibleCode divisorPasses
    rw [Bool.and_eq_true]
    refine ⟨by decide, ?_⟩
    rw [List.all_eq_true]
    intro d _
    by_cases hd32 : d < 32
    · interval_cases d <;> decide
    · simp only [Bool.or_eq_true, decide_eq_true_eq]
      left
      right
      rw [h283_log]
      have hlog : 5 ≤ Nat.log 2 d :=
        Nat.le_log_of_pow_le one_lt_two (by norm_num; omega)
      norm_num
      omega
  have h283 : (List.range' 283 1).find?
      (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = some 283 := by
    simp [h283_irreducible, h283_log]
  have hwindow :
      (List.range' 256 28).find?
          (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = some 283 := by
    rw [← List.range'_append_1 (s := 256) (m := 4) (n := 24), List.find?_append,
      h256, Option.none_or,
      ← List.range'_append_1 (s := 260) (m := 4) (n := 20), List.find?_append,
      h260, Option.none_or,
      ← List.range'_append_1 (s := 264) (m := 4) (n := 16), List.find?_append,
      h264, Option.none_or,
      ← List.range'_append_1 (s := 268) (m := 4) (n := 12), List.find?_append,
      h268, Option.none_or,
      ← List.range'_append_1 (s := 272) (m := 4) (n := 8), List.find?_append,
      h272, Option.none_or,
      ← List.range'_append_1 (s := 276) (m := 4) (n := 4), List.find?_append,
      h276, Option.none_or,
      ← List.range'_append_1 (s := 280) (m := 1) (n := 3), List.find?_append,
      h280, Option.none_or,
      ← List.range'_append_1 (s := 281) (m := 1) (n := 2), List.find?_append,
      h281, Option.none_or,
      ← List.range'_append_1 (s := 282) (m := 1) (n := 1), List.find?_append,
      h282, Option.none_or, h283]
  have hhigh :
      (List.range' 256 256).find?
          (fun m => Nat.log 2 m == 8 && isIrreducibleCode m) = some 283 := by
    rw [← List.range'_append_1 (s := 256) (m := 28) (n := 228), List.find?_append,
      hwindow, Option.some_or]
  unfold leastIrreducibleCode
  rw [show List.range 512 =
      List.range 256 ++ List.range' 256 256 by
        rw [List.range'_eq_map_range]
        simpa using (List.range_add (n := 256) (m := 256)),
    List.find?_append, hlow, Option.none_or, hhigh, Option.getD_some]

/-- The existing `BinaryField 8` uses the source modulus code `0x11b`. -/
theorem modulus_code : leastIrreducible 8 = polyOfCode 283 := by
  rw [← polyOfCode_leastIrreducibleCode (B := 512) (by norm_num) (by norm_num),
    leastIrreducibleCode_eight]

/-- The executable coefficient list is the modulus of `BinaryField 8`. -/
theorem polyOfBits_modulusBits : polyOfBits modulusBits = leastIrreducible 8 := by
  rw [modulusBits, modulusLow, show
      [true, true, false, true, true, false, false, false] ++ [true] = lowBits 9 283 by decide,
    polyOfBits_lowBits (by norm_num), ← modulus_code]

/-- The existing power-basis numbering of `BinaryField 8` by bytes. -/
@[expose] noncomputable def equivBinaryField : BinaryField 8 ≃ Byte :=
  BinaryField.equivFin (w := 8) (by norm_num)

/-- Interpret a byte as the corresponding element of `BinaryField 8`. -/
noncomputable def field (a : Byte) : BinaryField 8 := equivBinaryField.symm a

private theorem field_eq_mk (a : Byte) :
    field a = AdjoinRoot.mk (leastIrreducible 8) (polyOfBits (bits a)) := by
  rw [field, equivBinaryField, BinaryField.equivFin_symm_eq_mk_polyOfCode,
    ← polyOfBits_lowBits (width := 8) (code := a.val) (by omega)]
  rw [bits]

/-- Executable byte addition refines addition in `BinaryField 8`. -/
theorem field_add (input : Byte × Byte) :
    field (add input) = field input.1 + field input.2 := by
  rw [field_eq_mk, bits_add, polyOfBits_zipWith_xor (by simp), field_eq_mk, field_eq_mk,
    map_add]

/-- Executable shift-and-reduce multiplication refines multiplication in `BinaryField 8`. -/
theorem field_mul (input : Byte × Byte) :
    field (mul input) = field input.1 * field input.2 := by
  rw [field_eq_mk, bits_mul, field_eq_mk, field_eq_mk, ← map_mul]
  have h := mk_polyOfBits_foldl_modStep modulusLow (bits input.2) (bits input.1)
    (List.replicate 8 false) (by simp) (by simp)
  have hmod : polyOfBits (modulusLow ++ [true]) = leastIrreducible 8 := by
    simpa only [modulusBits] using polyOfBits_modulusBits
  rw [AdjoinRoot.mk_eq_mk] at h ⊢
  rw [← hmod]
  simpa only [modulusBits, polyOfBits_replicate_false, zero_add] using h

private theorem field_powFold (word : List Bool) (power accumulator : Byte) :
    field (word.foldl powStep (power, accumulator)).2 =
      field accumulator * field power ^ lsbValue word := by
  induction word generalizing power accumulator with
  | nil => simp [lsbValue]
  | cons bit word ih =>
    rw [List.foldl_cons, ih]
    cases bit
    · simp [powStep, field_mul, lsbValue, pow_mul, pow_two]
    · simp [powStep, field_mul, lsbValue, pow_add, pow_mul, pow_two]
      ring

private theorem field_one : field ⟨1, by norm_num⟩ = 1 := by
  rw [field_eq_mk, bits, polyOfBits_lowBits (by norm_num), polyOfCode_one]
  exact map_one _

/-- Executable square-and-multiply exponentiation refines exponentiation in `BinaryField 8`. -/
theorem field_pow (input : Byte × ℕ) :
    field (pow input) = field input.1 ^ input.2 := by
  rw [pow, field_powFold, lsbValue_bits]
  rw [field_one, one_mul]

/-- Executable exponent-254 inversion refines field inversion, including `0⁻¹ = 0`. -/
theorem field_inv (a : Byte) : field (inv a) = (field a)⁻¹ := by
  rw [inv, field_pow]
  by_cases ha : field a = 0
  · simp [ha]
  · have h := FiniteField.pow_card_sub_two_eq_inv (field a) ha
    rw [BinaryField.card (w := 8) (by norm_num)] at h
    norm_num at h ⊢
    exact h

/-- Executable total division refines field division, with division by zero equal to zero. -/
theorem field_div (input : Byte × Byte) :
    field (div input) = field input.1 / field input.2 := by
  rw [div, field_mul, field_inv, div_eq_mul_inv]

/-! ### Retained native byte machines -/

namespace Native

open Turing MultiTapeTM MultiTapeTM.Internal

/-- Constructive numeric encoding of an eight-bit finite-control word. -/
def wordStateEncoding : BitString 8 ↪ ℕ :=
  (BitString.equivFin 8).toEmbedding.trans Fin.valEmbedding

/-- The three phases of a fixed-width binary byte operation: read the left word, read the right
word, then emit the result. -/
inductive BinaryControl where
  | left (index : Fin 8) (word : BitString 8)
  | right (left : BitString 8) (index : Fin 8) (word : BitString 8)
  | emit (word : BitString 8) (index : Fin 8)
  deriving Fintype

/-- Constructive numeric encoding of every fixed-width binary-operation control state. -/
def binaryControlEncoding : BinaryControl ↪ ℕ := by
  let view : BinaryControl →
      (Fin 8 × BitString 8) ⊕
        ((BitString 8 × Fin 8 × BitString 8) ⊕ (BitString 8 × Fin 8))
    | .left index word => .inl (index, word)
    | .right left index word => .inr (.inl (left, index, word))
    | .emit word index => .inr (.inr (word, index))
  have hview : Function.Injective view := by
    intro left right h
    cases left <;> cases right <;> simp_all [view]
  exact (⟨view, hview⟩ : BinaryControl ↪
      (Fin 8 × BitString 8) ⊕
        ((BitString 8 × Fin 8 × BitString 8) ⊕ (BitString 8 × Fin 8))).trans
    (NativeCompiler.sumStateEncoding
      (NativeCompiler.prodStateEncoding Fin.valEmbedding wordStateEncoding)
      (NativeCompiler.sumStateEncoding
        (NativeCompiler.prodStateEncoding wordStateEncoding
          (NativeCompiler.prodStateEncoding Fin.valEmbedding wordStateEncoding))
        (NativeCompiler.prodStateEncoding wordStateEncoding Fin.valEmbedding)))

/-- Transition table for a fixed-width binary byte operation. -/
def binaryAction (f : Byte × Byte → Byte) (state : BinaryControl)
    (symbol : Option Bool) : Action 0 Bool BinaryControl :=
  match state with
  | .left index word =>
      let word' := Function.update word index (symbol.getD false)
      if h : index.val + 1 < 8 then
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.left ⟨index.val + 1, h⟩ word') }
      else
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.right word' ⟨0, by omega⟩ (fun _ => false)) }
  | .right left index word =>
      let word' := Function.update word index (symbol.getD false)
      if h : index.val + 1 < 8 then
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.right left ⟨index.val + 1, h⟩ word') }
      else
        let result := (BitString.equivFin 8).symm
          (f (BitString.equivFin 8 left, BitString.equivFin 8 word'))
        { inputTape := 1
          workTapes := Fin.elim0
          output := some (result ⟨0, by omega⟩)
          state := some (.emit result ⟨1, by omega⟩) }
  | .emit word index =>
      if h : index.val + 1 < 8 then
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := some (.emit word ⟨index.val + 1, h⟩) }
      else
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := none }

/-- Direct zero-work-tape table for a fixed-width binary byte operation.  Its transition function
contains the operation at the unique point where both eight-bit operands have been read. -/
def binaryCoreTable (f : Byte × Byte → Byte) :
    MultiTapeMachine 0 Bool BinaryControl Empty Id :=
  MultiTapeMachine.ofTr (.left ⟨0, by omega⟩ (fun _ => false)) fun state symbol _ =>
    binaryAction f state symbol

/-- Retained tidy table for a fixed-width binary byte operation: execute the direct core, then
return the input head to its canonical starting position. -/
def binaryTable (f : Byte × Byte → Byte) :
    MultiTapeMachine 0 Bool (BinaryControl ⊕ RewindState) Empty Id :=
  (binaryCoreTable f).seq (MultiTapeMachine.rewindInput Bool)

private def binaryCfg (input : List Bool) (state : Option BinaryControl)
    (position : Fin (input.length + 2)) (output : List Bool) :
    Cfg 0 Bool BinaryControl input :=
  { state := state
    inputPos := position
    workTapes := fun i => Fin.elim0 i
    workTapePos := fun i => Fin.elim0 i
    output := output }

private theorem step_binaryCfg (f : Byte × Byte → Byte) (input : List Bool)
    (state : BinaryControl) (position : Fin (input.length + 2)) (output : List Bool) :
    (binaryCoreTable f).toTM.step (binaryCfg input (some state) position output) =
      let action := binaryAction f state (inputAt input position.val)
      binaryCfg input action.state (moveInputPos position action.inputTape)
        (output ++ action.output.toList) := by
  rw [MultiTapeTM.step_of_state rfl, binaryCoreTable, MultiTapeMachine.toTM_ofTr,
    MultiTapeTM.tr_ofTr]
  rw [Cfg.inputSymbol_eq_inputAt]
  apply Cfg.ext_zero_tapes <;> rfl

private abbrev zeroWord : BitString 8 := fun _ => false

-- `decide` checks the 256 byte values; its proof term has a deeper reduction spine than the
-- default elaborator limit even though the finite check is small.
set_option maxRecDepth 2048 in
private theorem loadedWord_eq (a : Byte) :
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update zeroWord 0 (decide (a.val % 2 = 1)))
                  1 (a.val.testBit 1))
                2 (a.val.testBit 2))
              3 (a.val.testBit 3))
            4 (a.val.testBit 4))
          5 (a.val.testBit 5))
        6 (a.val.testBit 6))
      7 (a.val.testBit 7) = (BitString.equivFin 8).symm a := by
  revert a
  decide

private theorem readLeft_eight (f : Byte × Byte → Byte) (input : Byte × Byte) :
    (binaryCoreTable f).toTM.step^[8]
        (binaryCfg (pairBits input) (some (.left ⟨0, by omega⟩ zeroWord))
          ⟨1, by simp⟩ []) =
      binaryCfg (pairBits input)
        (some (.right ((BitString.equivFin 8).symm input.1) ⟨0, by omega⟩ zeroWord))
        ⟨9, by simp⟩ [] := by
  norm_num [Function.iterate_succ_apply', step_binaryCfg, binaryAction, pairBits, bits,
    lowBits_eq_ofFn_equivFin_symm, Function.update, inputAt, moveInputPos, zeroWord,
    loadedWord_eq]

private theorem readRight_eight (f : Byte × Byte → Byte) (input : Byte × Byte) :
    let result := (BitString.equivFin 8).symm (f input)
    (binaryCoreTable f).toTM.step^[8]
        (binaryCfg (pairBits input)
          (some (.right ((BitString.equivFin 8).symm input.1) ⟨0, by omega⟩ zeroWord))
          ⟨9, by simp⟩ []) =
      binaryCfg (pairBits input) (some (.emit result ⟨1, by omega⟩)) ⟨17, by simp⟩
        [result ⟨0, by omega⟩] := by
  norm_num [Function.iterate_succ_apply', step_binaryCfg, binaryAction, pairBits, bits,
    lowBits_eq_ofFn_equivFin_symm, Function.update, inputAt, moveInputPos, zeroWord,
    loadedWord_eq]

private theorem emitRemaining_seven (f : Byte × Byte → Byte) (input : Byte × Byte) :
    let result := (BitString.equivFin 8).symm (f input)
    (binaryCoreTable f).toTM.step^[7]
        (binaryCfg (pairBits input) (some (.emit result ⟨1, by omega⟩)) ⟨17, by simp⟩
          [result ⟨0, by omega⟩]) =
      binaryCfg (pairBits input) none ⟨17, by simp⟩ (List.ofFn result) := by
  norm_num [Function.iterate_succ_apply', step_binaryCfg, binaryAction, moveInputPos,
    List.ofFn_succ]

/-- The retained binary byte table consumes sixteen input bits, emits eight result bits, rewinds
the input head, uses no work tape and halts within forty-one allowed steps. -/
theorem computesTidily_binaryTable (f : Byte × Byte → Byte) (input : Byte × Byte) :
    (binaryTable f).toTM.ComputesTidilyInTimeAndSpace
      (pairBits input) (bits (f input)) 41 0 := by
  let start := (binaryCoreTable f).toTM.initCfg (pairBits input)
  let path := MultiTapeNTM.RunPath.ofDeterministic (binaryCoreTable f).toTM start 23
  have hstart : start =
      binaryCfg (pairBits input) (some (.left ⟨0, by omega⟩ zeroWord)) ⟨1, by simp⟩ [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hlast : path.last =
      binaryCfg (pairBits input) none ⟨17, by simp⟩
        (List.ofFn ((BitString.equivFin 8).symm (f input))) := by
    rw [MultiTapeTM.runPath_last_eq_runFrom]
    change (binaryCoreTable f).toTM.step^[23] start = _
    rw [hstart, show 23 = 7 + (8 + 8) by omega, Function.iterate_add_apply,
      Function.iterate_add_apply, readLeft_eight, readRight_eight, emitRemaining_seven]
  have htidy := computesTidily_seq_explicitRewind_of_runPath (path := path)
    (show path.head = wordsCfg (pairBits input)
        (some (binaryCoreTable f).toTM.q₀) (fun _ => []) [] by
      change start = _
      exact (binaryCoreTable f).toTM.initCfg_eq_wordsCfg (pairBits input))
    (show path.last.Halted by rw [hlast]; rfl)
  rw [hlast] at htidy
  rw [show path.time = 23 by rfl] at htidy
  simpa [binaryTable, MultiTapeMachine.toTM_seq, binaryCfg, bits,
    lowBits_eq_ofFn_equivFin_symm] using htidy

/-- Named compiler retaining the direct fixed-width operation table, its exact state encoding and
the core-plus-rewind table.  In particular, `staticBits` charges the table hardwired by `f`. -/
@[expose] def binaryCompiler (f : Byte × Byte → Byte) :
    NativeCompiler f pairEncoding encoding :=
  { tapeCount := 0
    State := BinaryControl ⊕ RewindState
    table := binaryTable f
    stateEncoding := NativeCompiler.sumStateEncoding binaryControlEncoding
      NativeCompiler.rewindStateEncoding
    time := fun _ => 41
    workspace := fun _ => 0
    computes := fun input => by
      change (binaryTable f).toTM.ComputesTidilyInTimeAndSpace
        (pairBits input) (bits (f input)) 41 0
      exact computesTidily_binaryTable f input }

/-- Every retained fixed-width binary byte compiler gives an asymptotic polynomial-time witness;
the concrete witness remains `binaryCompiler f`, including its exact `staticBits` charge. -/
theorem computableInPolyTime_binary (f : Byte × Byte → Byte) :
    ComputableInPolyTime f pairEncoding encoding := by
  apply ComputableInTimeAndSpace.computableInPolyTime (t := fun _ => 41) (by fun_prop)
  exact (binaryCompiler f).computableInTimeAndSpace

/-- Retained native compiler for executable GF(256) addition. -/
@[expose] def addCompiler : NativeCompiler add pairEncoding encoding :=
  binaryCompiler add

/-- Retained native compiler for executable GF(256) multiplication. -/
@[expose] def mulCompiler : NativeCompiler mul pairEncoding encoding :=
  binaryCompiler mul

/-- Retained native compiler for executable total GF(256) division. -/
@[expose] def divCompiler : NativeCompiler div pairEncoding encoding :=
  binaryCompiler div

/-! ### Retained unary byte operations -/

/-- The two phases of a fixed-width unary byte operation: read its byte, then emit the result. -/
inductive UnaryControl where
  | read (index : Fin 8) (word : BitString 8)
  | emit (word : BitString 8) (index : Fin 8)
  deriving Fintype

/-- The constructor-level representation used by both the unary state encoding and its checked
cardinality. -/
private def unaryControlEquiv : UnaryControl ≃
    (Fin 8 × BitString 8) ⊕ (BitString 8 × Fin 8) :=
  { toFun
      | .read index word => .inl (index, word)
      | .emit word index => .inr (word, index)
    invFun
      | .inl (index, word) => .read index word
      | .inr (word, index) => .emit word index
    left_inv := by intro state; cases state <;> rfl
    right_inv := by
      intro state
      rcases state with state | state <;> rcases state with ⟨_, _⟩ <;> rfl }

/-- Constructive numeric encoding of every unary-operation control state. -/
def unaryControlEncoding : UnaryControl ↪ ℕ :=
  unaryControlEquiv.toEmbedding.trans
    (NativeCompiler.sumStateEncoding
      (NativeCompiler.prodStateEncoding Fin.valEmbedding wordStateEncoding)
      (NativeCompiler.prodStateEncoding wordStateEncoding Fin.valEmbedding))

/-- Transition table for a fixed-width unary byte operation. -/
def unaryAction (f : Byte → Byte) (state : UnaryControl)
    (symbol : Option Bool) : Action 0 Bool UnaryControl :=
  match state with
  | .read index word =>
      let word' := Function.update word index (symbol.getD false)
      if h : index.val + 1 < 8 then
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.read ⟨index.val + 1, h⟩ word') }
      else
        let result := (BitString.equivFin 8).symm (f (BitString.equivFin 8 word'))
        { inputTape := 1
          workTapes := Fin.elim0
          output := some (result ⟨0, by omega⟩)
          state := some (.emit result ⟨1, by omega⟩) }
  | .emit word index =>
      if h : index.val + 1 < 8 then
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := some (.emit word ⟨index.val + 1, h⟩) }
      else
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := none }

/-- Direct zero-work-tape table for a fixed-width unary byte operation. -/
def unaryCoreTable (f : Byte → Byte) :
    MultiTapeMachine 0 Bool UnaryControl Empty Id :=
  MultiTapeMachine.ofTr (.read ⟨0, by omega⟩ (fun _ => false)) fun state symbol _ =>
    unaryAction f state symbol

/-- Retained tidy table for a fixed-width unary byte operation. -/
def unaryTable (f : Byte → Byte) :
    MultiTapeMachine 0 Bool (UnaryControl ⊕ RewindState) Empty Id :=
  (unaryCoreTable f).seq (MultiTapeMachine.rewindInput Bool)

private def unaryCfg (input : List Bool) (state : Option UnaryControl)
    (position : Fin (input.length + 2)) (output : List Bool) :
    Cfg 0 Bool UnaryControl input :=
  { state := state
    inputPos := position
    workTapes := fun i => Fin.elim0 i
    workTapePos := fun i => Fin.elim0 i
    output := output }

private theorem step_unaryCfg (f : Byte → Byte) (input : List Bool)
    (state : UnaryControl) (position : Fin (input.length + 2)) (output : List Bool) :
    (unaryCoreTable f).toTM.step (unaryCfg input (some state) position output) =
      let action := unaryAction f state (inputAt input position.val)
      unaryCfg input action.state (moveInputPos position action.inputTape)
        (output ++ action.output.toList) := by
  rw [MultiTapeTM.step_of_state rfl, unaryCoreTable, MultiTapeMachine.toTM_ofTr,
    MultiTapeTM.tr_ofTr]
  rw [Cfg.inputSymbol_eq_inputAt]
  apply Cfg.ext_zero_tapes <;> rfl

private theorem unary_read_eight (f : Byte → Byte) (input : Byte) :
    let result := (BitString.equivFin 8).symm (f input)
    (unaryCoreTable f).toTM.step^[8]
        (unaryCfg (bits input) (some (.read ⟨0, by omega⟩ zeroWord))
          ⟨1, by simp⟩ []) =
      unaryCfg (bits input) (some (.emit result ⟨1, by omega⟩)) ⟨9, by simp⟩
        [result ⟨0, by omega⟩] := by
  norm_num [Function.iterate_succ_apply', step_unaryCfg, unaryAction, bits,
    lowBits_eq_ofFn_equivFin_symm, Function.update, inputAt, moveInputPos, zeroWord,
    loadedWord_eq]

private theorem unary_emitRemaining_seven (f : Byte → Byte) (input : Byte) :
    let result := (BitString.equivFin 8).symm (f input)
    (unaryCoreTable f).toTM.step^[7]
        (unaryCfg (bits input) (some (.emit result ⟨1, by omega⟩)) ⟨9, by simp⟩
          [result ⟨0, by omega⟩]) =
      unaryCfg (bits input) none ⟨9, by simp⟩ (List.ofFn result) := by
  norm_num [Function.iterate_succ_apply', step_unaryCfg, unaryAction, moveInputPos,
    List.ofFn_succ]

/-- A retained unary byte table consumes eight bits, emits eight bits, rewinds its input head,
uses no work tape and halts within twenty-five allowed steps. -/
theorem computesTidily_unaryTable (f : Byte → Byte) (input : Byte) :
    (unaryTable f).toTM.ComputesTidilyInTimeAndSpace (bits input) (bits (f input)) 25 0 := by
  let start := (unaryCoreTable f).toTM.initCfg (bits input)
  let path := MultiTapeNTM.RunPath.ofDeterministic (unaryCoreTable f).toTM start 15
  have hstart : start =
      unaryCfg (bits input) (some (.read ⟨0, by omega⟩ zeroWord)) ⟨1, by simp⟩ [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hlast : path.last =
      unaryCfg (bits input) none ⟨9, by simp⟩
        (List.ofFn ((BitString.equivFin 8).symm (f input))) := by
    rw [MultiTapeTM.runPath_last_eq_runFrom]
    change (unaryCoreTable f).toTM.step^[15] start = _
    rw [hstart, show 15 = 7 + 8 by omega, Function.iterate_add_apply,
      unary_read_eight, unary_emitRemaining_seven]
  have htidy := computesTidily_seq_explicitRewind_of_runPath (path := path)
    (show path.head = wordsCfg (bits input)
        (some (unaryCoreTable f).toTM.q₀) (fun _ => []) [] by
      change start = _
      exact (unaryCoreTable f).toTM.initCfg_eq_wordsCfg (bits input))
    (show path.last.Halted by rw [hlast]; rfl)
  rw [hlast] at htidy
  rw [show path.time = 15 by rfl] at htidy
  simpa [unaryTable, MultiTapeMachine.toTM_seq, unaryCfg, bits,
    lowBits_eq_ofFn_equivFin_symm] using htidy

/-- Named compiler retaining a fixed-width unary byte table and its exact resources. -/
@[expose] def unaryCompiler (f : Byte → Byte) : NativeCompiler f encoding encoding :=
  { tapeCount := 0
    State := UnaryControl ⊕ RewindState
    table := unaryTable f
    stateEncoding := NativeCompiler.sumStateEncoding unaryControlEncoding
      NativeCompiler.rewindStateEncoding
    time := fun _ => 25
    workspace := fun _ => 0
    computes := fun input => by
      change (unaryTable f).toTM.ComputesTidilyInTimeAndSpace
        (bits input) (bits (f input)) 25 0
      exact computesTidily_unaryTable f input }

/-- Every retained fixed-width unary byte compiler gives an asymptotic polynomial-time witness;
the concrete witness remains `unaryCompiler f`, including its exact `staticBits` charge. -/
theorem computableInPolyTime_unary (f : Byte → Byte) :
    ComputableInPolyTime f encoding encoding := by
  apply ComputableInTimeAndSpace.computableInPolyTime (t := fun _ => 25) (by fun_prop)
  exact (unaryCompiler f).computableInTimeAndSpace

/-- Retained native compiler for executable total GF(256) inversion, including its concrete clock,
zero workspace bound and exact `staticBits` program-description charge. -/
@[expose] def invCompiler : NativeCompiler inv encoding encoding :=
  unaryCompiler inv

/-! ### Retained streaming exponentiation -/

/-- The phases of streaming exponentiation: read the base, fold exponent bits, then emit. -/
inductive PowControl where
  | base (index : Fin 8) (word : BitString 8)
  | exponent (state : Byte × Byte)
  | emit (word : BitString 8) (index : Fin 8)
  deriving Fintype

/-- The constructor-level representation used by both the exponentiation state encoding and its
checked cardinality. -/
private def powControlEquiv : PowControl ≃
    (Fin 8 × BitString 8) ⊕ ((Byte × Byte) ⊕ (BitString 8 × Fin 8)) :=
  { toFun
      | .base index word => .inl (index, word)
      | .exponent state => .inr (.inl state)
      | .emit word index => .inr (.inr (word, index))
    invFun
      | .inl (index, word) => .base index word
      | .inr (.inl state) => .exponent state
      | .inr (.inr (word, index)) => .emit word index
    left_inv := by intro state; cases state <;> rfl
    right_inv := by
      intro state
      rcases state with state | state
      · rcases state with ⟨_, _⟩; rfl
      · rcases state with state | state <;> rcases state with ⟨_, _⟩ <;> rfl }

/-- Constructive numeric encoding of every streaming-exponentiation control state. -/
def powControlEncoding : PowControl ↪ ℕ :=
  powControlEquiv.toEmbedding.trans
    (NativeCompiler.sumStateEncoding
      (NativeCompiler.prodStateEncoding Fin.valEmbedding wordStateEncoding)
      (NativeCompiler.sumStateEncoding
        (NativeCompiler.prodStateEncoding Fin.valEmbedding Fin.valEmbedding)
        (NativeCompiler.prodStateEncoding wordStateEncoding Fin.valEmbedding)))

/-- Transition table for streaming exponentiation. -/
def powAction (state : PowControl) (symbol : Option Bool) :
    Action 0 Bool PowControl :=
  match state with
  | .base index word =>
      let word' := Function.update word index (symbol.getD false)
      if h : index.val + 1 < 8 then
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.base ⟨index.val + 1, h⟩ word') }
      else
        { inputTape := 1
          workTapes := Fin.elim0
          output := none
          state := some (.exponent (BitString.equivFin 8 word', ⟨1, by norm_num⟩)) }
  | .exponent foldState =>
      match symbol with
      | some bit =>
          { inputTape := 1
            workTapes := Fin.elim0
            output := none
            state := some (.exponent (powStep foldState bit)) }
      | none =>
          let result := (BitString.equivFin 8).symm foldState.2
          { inputTape := 0
            workTapes := Fin.elim0
            output := some (result ⟨0, by omega⟩)
            state := some (.emit result ⟨1, by omega⟩) }
  | .emit word index =>
      if h : index.val + 1 < 8 then
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := some (.emit word ⟨index.val + 1, h⟩) }
      else
        { inputTape := 0
          workTapes := Fin.elim0
          output := some (word index)
          state := none }

/-- Direct zero-work-tape table for streaming exponentiation. -/
def powCoreTable : MultiTapeMachine 0 Bool PowControl Empty Id :=
  MultiTapeMachine.ofTr (.base ⟨0, by omega⟩ (fun _ => false)) fun state symbol _ =>
    powAction state symbol

/-- Retained tidy table that reads a raw base byte and streams the little-endian exponent bits. -/
def powTable : MultiTapeMachine 0 Bool (PowControl ⊕ RewindState) Empty Id :=
  powCoreTable.seq (MultiTapeMachine.rewindInput Bool)

private def powCfg (input : List Bool) (state : Option PowControl)
    (position : Fin (input.length + 2)) (output : List Bool) : Cfg 0 Bool PowControl input :=
  { state := state
    inputPos := position
    workTapes := fun i => Fin.elim0 i
    workTapePos := fun i => Fin.elim0 i
    output := output }

private theorem step_powCfg (input : List Bool) (state : PowControl)
    (position : Fin (input.length + 2)) (output : List Bool) :
    powCoreTable.toTM.step (powCfg input (some state) position output) =
      let action := powAction state (inputAt input position.val)
      powCfg input action.state (moveInputPos position action.inputTape)
        (output ++ action.output.toList) := by
  rw [MultiTapeTM.step_of_state rfl, powCoreTable, MultiTapeMachine.toTM_ofTr,
    MultiTapeTM.tr_ofTr]
  rw [Cfg.inputSymbol_eq_inputAt]
  apply Cfg.ext_zero_tapes <;> rfl

private theorem pow_readBase_eight (input : Byte × ℕ) :
    powCoreTable.toTM.step^[8]
        (powCfg (powBits input) (some (.base ⟨0, by omega⟩ zeroWord))
          ⟨1, by simp⟩ []) =
      powCfg (powBits input)
        (some (.exponent (input.1, ⟨1, by norm_num⟩)))
        ⟨9, by rw [length_powBits]; omega⟩ [] := by
  norm_num [Function.iterate_succ_apply', step_powCfg, powAction, powBits, bits,
    lowBits_eq_ofFn_equivFin_symm, Function.update, inputAt, moveInputPos, zeroWord,
    loadedWord_eq]

private theorem pow_scan_prefix (input : Byte × ℕ) (r : ℕ)
    (hr : r ≤ input.2.bits.length) :
    powCoreTable.toTM.step^[r]
        (powCfg (powBits input)
          (some (.exponent (input.1, ⟨1, by norm_num⟩)))
          ⟨9, by rw [length_powBits]; omega⟩ []) =
      powCfg (powBits input)
        (some (.exponent ((input.2.bits.take r).foldl powStep
          (input.1, ⟨1, by norm_num⟩)))) ⟨9 + r, by simp [powBits]; omega⟩ [] := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hrlt : r < input.2.bits.length := by omega
      rw [Function.iterate_succ_apply', ih (by omega), step_powCfg]
      have hsymbol : inputAt (powBits input) (9 + r) = some input.2.bits[r] := by
        rw [show 9 + r = (8 + r) + 1 by omega, inputAt_succ, powBits,
          List.getElem?_append_right (by simp)]
        simp only [length_bits, Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem hrlt
      simp only [powAction, hsymbol, Option.toList_none, List.append_nil]
      rw [List.take_succ_eq_append_getElem hrlt, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      apply congrArg (fun position => powCfg (powBits input)
        (some (.exponent (powStep ((input.2.bits.take r).foldl powStep
          (input.1, ⟨1, by norm_num⟩)) input.2.bits[r]))) position [])
      apply Fin.ext
      rw [val_moveInputPos_eq_moveInputPosNat]
      simp [moveInputPosNat]
      omega

private theorem pow_scan_all (input : Byte × ℕ) :
    powCoreTable.toTM.step^[input.2.bits.length]
        (powCfg (powBits input)
          (some (.exponent (input.1, ⟨1, by norm_num⟩)))
          ⟨9, by rw [length_powBits]; omega⟩ []) =
      powCfg (powBits input)
        (some (.exponent (input.2.bits.foldl powStep
          (input.1, ⟨1, by norm_num⟩))))
        ⟨(powBits input).length + 1, by omega⟩ [] := by
  convert pow_scan_prefix input input.2.bits.length le_rfl using 1
  rw [List.take_of_length_le le_rfl]
  apply congrArg (fun position => powCfg (powBits input)
    (some (.exponent (input.2.bits.foldl powStep
      (input.1, ⟨1, by norm_num⟩)))) position [])
  apply Fin.ext
  change (powBits input).length + 1 = 9 + input.2.bits.length
  simp only [length_powBits]
  omega

private theorem step_pow_emit (input : List Bool) (result : BitString 8)
    (index : Fin 8) (position : Fin (input.length + 2)) (output : List Bool) :
    powCoreTable.toTM.step (powCfg input (some (.emit result index)) position output) =
      if h : index.val + 1 < 8 then
        powCfg input (some (.emit result ⟨index.val + 1, h⟩)) position
          (output ++ [result index])
      else
        powCfg input none position (output ++ [result index]) := by
  rw [step_powCfg]
  by_cases h : index.val + 1 < 8
  · simp [powAction, h]
  · simp [powAction, h]

private theorem pow_emitFirst_three (input : Byte × ℕ) (result : BitString 8) :
    powCoreTable.toTM.step^[3]
        (powCfg (powBits input) (some (.emit result ⟨1, by omega⟩))
          ⟨(powBits input).length + 1, by omega⟩
          [result ⟨0, by omega⟩]) =
      powCfg (powBits input) (some (.emit result ⟨4, by omega⟩))
        ⟨(powBits input).length + 1, by omega⟩
        [result ⟨0, by omega⟩, result ⟨1, by omega⟩,
          result ⟨2, by omega⟩, result ⟨3, by omega⟩] := by
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  norm_num

private theorem pow_emitLast_four (input : Byte × ℕ) (result : BitString 8) :
    powCoreTable.toTM.step^[4]
        (powCfg (powBits input) (some (.emit result ⟨4, by omega⟩))
          ⟨(powBits input).length + 1, by omega⟩
          [result ⟨0, by omega⟩, result ⟨1, by omega⟩,
            result ⟨2, by omega⟩, result ⟨3, by omega⟩]) =
      powCfg (powBits input) none ⟨(powBits input).length + 1, by omega⟩
        (List.ofFn result) := by
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_left (by norm_num)]
  rw [Function.iterate_succ_apply, step_pow_emit, dite_eq_right (by norm_num),
    Function.iterate_zero_apply]
  norm_num [List.ofFn_succ]

private theorem pow_finish_eight (input : Byte × ℕ) :
    let foldState := input.2.bits.foldl powStep (input.1, ⟨1, by norm_num⟩)
    let result := (BitString.equivFin 8).symm foldState.2
    powCoreTable.toTM.step^[8]
        (powCfg (powBits input) (some (.exponent foldState))
          ⟨(powBits input).length + 1, by omega⟩ []) =
      powCfg (powBits input) none ⟨(powBits input).length + 1, by omega⟩
        (List.ofFn result) := by
  have hblank : inputAt (powBits input) ((powBits input).length + 1) = none :=
    (inputAt_eq_none_iff (powBits input) _).2 (Or.inr (by omega))
  dsimp only
  change powCoreTable.toTM.step^[7 + 1]
      (powCfg (powBits input)
        (some (.exponent (input.2.bits.foldl powStep (input.1, ⟨1, by norm_num⟩))))
        ⟨(powBits input).length + 1, by omega⟩ []) = _
  rw [Function.iterate_add_apply, Function.iterate_one, step_powCfg]
  simp only [powAction, hblank, Option.toList_some, List.nil_append, moveInputPos_zero]
  rw [show 7 = 4 + 3 by omega, Function.iterate_add_apply, pow_emitFirst_three,
    pow_emitLast_four]

/-- The retained exponentiation table streams its unframed exponent, emits eight result bits,
uses no work tape and has exact affine time in the encoded input length. -/
theorem computesTidily_powTable (input : Byte × ℕ) :
    powTable.toTM.ComputesTidilyInTimeAndSpace
      (powBits input) (bits (pow input)) (2 * (powBits input).length + 10) 0 := by
  let start := powCoreTable.toTM.initCfg (powBits input)
  let coreTime := (powBits input).length + 8
  let path := MultiTapeNTM.RunPath.ofDeterministic powCoreTable.toTM start coreTime
  have hstart : start =
      powCfg (powBits input) (some (.base ⟨0, by omega⟩ zeroWord)) ⟨1, by simp⟩ [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hlast : path.last =
      powCfg (powBits input) none ⟨(powBits input).length + 1, by omega⟩
        (List.ofFn ((BitString.equivFin 8).symm (pow input))) := by
    rw [MultiTapeTM.runPath_last_eq_runFrom]
    change powCoreTable.toTM.step^[coreTime] start = _
    rw [show coreTime = 8 + (input.2.bits.length + 8) by
          simp [coreTime, length_powBits]; omega,
      hstart, Function.iterate_add_apply, Function.iterate_add_apply,
      pow_readBase_eight, pow_scan_all, pow_finish_eight]
    rfl
  have htidy := computesTidily_seq_explicitRewind_of_runPath (path := path)
    (show path.head = wordsCfg (powBits input) (some powCoreTable.toTM.q₀) (fun _ => []) [] by
      change start = _
      exact powCoreTable.toTM.initCfg_eq_wordsCfg (powBits input))
    (show path.last.Halted by rw [hlast]; rfl)
  rw [hlast] at htidy
  rw [show path.time = coreTime by rfl] at htidy
  have htime :
      coreTime + ((powBits input).length + 1 - 1 + 2) =
        2 * (powBits input).length + 10 := by
    dsimp [coreTime]
    omega
  dsimp only [powCfg] at htidy
  rw [htime] at htidy
  simpa [powTable, MultiTapeMachine.toTM_seq, powCfg, pow, coreTime, bits,
    lowBits_eq_ofFn_equivFin_symm] using htidy

/-- Named compiler retaining the streaming exponentiation table and its concrete affine clock,
zero workspace bound and exact `staticBits` program-description charge. -/
@[expose] def powCompiler : NativeCompiler pow powEncoding encoding :=
  { tapeCount := 0
    State := PowControl ⊕ RewindState
    table := powTable
    stateEncoding := NativeCompiler.sumStateEncoding powControlEncoding
      NativeCompiler.rewindStateEncoding
    time := fun input => 2 * (powBits input).length + 10
    workspace := fun _ => 0
    computes := fun input => by
      change powTable.toTM.ComputesTidilyInTimeAndSpace
        (powBits input) (bits (pow input)) (2 * (powBits input).length + 10) 0
      exact computesTidily_powTable input }

private def rewindStateEquiv : RewindState ≃ Bool :=
  { toFun
      | .start => false
      | .walk => true
    invFun
      | false => .start
      | true => .walk
    left_inv := by intro state; cases state <;> rfl
    right_inv := by intro state; cases state <;> rfl }

private theorem card_unaryCompilerState
    (inst : Fintype (UnaryControl ⊕ RewindState)) :
    @Fintype.card (UnaryControl ⊕ RewindState) inst = 4098 := by
  calc
    @Fintype.card (UnaryControl ⊕ RewindState) inst =
        Fintype.card (((Fin 8 × BitString 8) ⊕ (BitString 8 × Fin 8)) ⊕ Bool) :=
      @Fintype.card_congr _ _ inst inferInstance
        (Equiv.sumCongr unaryControlEquiv rewindStateEquiv)
    _ = 4098 := by norm_num

private theorem card_powCompilerState (inst : Fintype (PowControl ⊕ RewindState)) :
    @Fintype.card (PowControl ⊕ RewindState) inst = 69634 := by
  calc
    @Fintype.card (PowControl ⊕ RewindState) inst =
        Fintype.card
          (((Fin 8 × BitString 8) ⊕ ((Byte × Byte) ⊕ (BitString 8 × Fin 8))) ⊕
            Bool) :=
      @Fintype.card_congr _ _ inst inferInstance
        (Equiv.sumCongr powControlEquiv rewindStateEquiv)
    _ = 69634 := by norm_num

/-- The inversion compiler takes 25 steps and zero workspace, has 4,098 states and 12,294
transition rows.  Its final inequality charges the complete encoded program without expanding
the large finite table to a decimal. -/
theorem invCompiler_resourceBounds :
    (∀ input, invCompiler.time input = 25 ∧ invCompiler.workspace input = 0) ∧
      invCompiler.tapeCount = 0 ∧
      Fintype.card (UnaryControl ⊕ RewindState) = 4098 ∧
      invCompiler.description.table.length = 12294 ∧
      invCompiler.staticBits ≤
        2 * invCompiler.tapeCount + 2 * invCompiler.stateBound + 2 +
          12294 * (2 * invCompiler.maxEntryBits + 1) := by
  have hcard : Fintype.card (UnaryControl ⊕ RewindState) = 4098 := by
    exact card_unaryCompilerState inferInstance
  have hcompilerCard :
      @Fintype.card invCompiler.State invCompiler.stateFintype = 4098 := by
    exact card_unaryCompilerState invCompiler.stateFintype
  have htapeCount : invCompiler.tapeCount = 0 := rfl
  have hrows : invCompiler.description.table.length = 12294 := by
    have h := NativeCompiler.description_table_length invCompiler
    rw [hcompilerCard, htapeCount] at h
    norm_num at h
    exact h
  refine ⟨fun _ => ⟨rfl, rfl⟩, htapeCount, hcard, hrows, ?_⟩
  have hstatic := NativeCompiler.staticBits_le invCompiler
  rw [hrows] at hstatic
  exact hstatic

/-- The exponentiation compiler takes twice the encoded input length plus 10 steps and zero
workspace, and has 69,634 states and 208,902 transition rows.  Its final inequality charges the
complete encoded program without expanding the large finite table to a decimal. -/
theorem powCompiler_resourceBounds :
    (∀ input, powCompiler.time input = 2 * (powEncoding input).length + 10 ∧
      powCompiler.workspace input = 0) ∧
      powCompiler.tapeCount = 0 ∧
      Fintype.card (PowControl ⊕ RewindState) = 69634 ∧
      powCompiler.description.table.length = 208902 ∧
      powCompiler.staticBits ≤
        2 * powCompiler.tapeCount + 2 * powCompiler.stateBound + 2 +
          208902 * (2 * powCompiler.maxEntryBits + 1) := by
  have hcard : Fintype.card (PowControl ⊕ RewindState) = 69634 := by
    exact card_powCompilerState inferInstance
  have hcompilerCard :
      @Fintype.card powCompiler.State powCompiler.stateFintype = 69634 := by
    exact card_powCompilerState powCompiler.stateFintype
  have htapeCount : powCompiler.tapeCount = 0 := rfl
  have hrows : powCompiler.description.table.length = 208902 := by
    have h := NativeCompiler.description_table_length powCompiler
    rw [hcompilerCard, htapeCount] at h
    norm_num at h
    exact h
  refine ⟨fun _ => ⟨rfl, rfl⟩, htapeCount, hcard, hrows, ?_⟩
  have hstatic := NativeCompiler.staticBits_le powCompiler
  rw [hrows] at hstatic
  exact hstatic

/-- Streaming GF(256) exponentiation is computable in polynomial time by `powCompiler`. -/
theorem computableInPolyTime_pow : ComputableInPolyTime pow powEncoding encoding := by
  apply ComputableInTimeAndSpace.computableInPolyTime (t := fun n => 2 * n + 10) (by fun_prop)
  exact powCompiler.computableInTimeAndSpace

end Native

end Cslib.GF256
