/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldTable
public import CslibFrontier.Foundations.Data.Nat.FindCode
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.GetD

/-!
# Table-free multiplication in explicit binary fields

Multiplication scans one operand's coefficient word, shifting the other modulo the supplied
polynomial and accumulating the product. Both live words have the degree of the modulus at
every scan boundary, by `Cslib.modMulBits_spec`.

## Main definitions

* `Cslib.BinaryField.modulusBitsScan`: modulus search by bounded counters.
* `Cslib.BinaryField.fieldMulMod`: table-free multiplication with a supplied modulus.

## Main results

* `Cslib.BinaryField.fieldOfBits_fieldMulMod`: correctness for the explicit binary field.
-/

public section

namespace Cslib.BinaryField

open Polynomial BitString

private theorem all_range_eq_isNone_findCode (p : ℕ → Bool) (n : ℕ) :
    (List.range n).all p = (findCode (fun d => !p d) 0 n).isNone := by
  rw [findCode_eq, ← List.range_eq_range']
  apply Bool.eq_iff_iff.mpr
  simp [List.all_eq_true, Option.isNone_iff_eq_none]

private def isIrreducibleCodeScan (m : ℕ) : Bool :=
  decide (2 ≤ m) && (findCode (fun d => !divisorPasses m d) 0 m).isNone

private theorem isIrreducibleCodeScan_eq (m : ℕ) :
    isIrreducibleCodeScan m = isIrreducibleCode m := by
  rw [isIrreducibleCodeScan, isIrreducibleCode, all_range_eq_isNone_findCode]

/-- Search for the modulus in code order using a candidate and a trial divisor counter,
without allocating lists of candidates or divisors. -/
def modulusBitsScan (w : ℕ) : List Bool :=
  ((findCode (fun m => Nat.log 2 m == w && isIrreducibleCodeScan m) 0 (2 ^ (w + 1))).getD 0).bits

/-- The outer search uses the same degree and irreducibility predicate as the modulus
specification. A native irreducibility test can therefore supply the predicate directly. -/
theorem modulusBitsScan_eq_findCode (w : ℕ) :
    modulusBitsScan w =
      ((findCode (fun m => Nat.log 2 m == w && isIrreducibleCode m) 0
        (2 ^ (w + 1))).getD 0).bits := by
  simp only [modulusBitsScan, isIrreducibleCodeScan_eq]

/-- The counter scan selects exactly the modulus used by the table-based evaluator. -/
theorem modulusBitsScan_eq (w : ℕ) : modulusBitsScan w = modulusBits w := by
  simp [modulusBitsScan_eq_findCode, findCode_eq, ← List.range_eq_range',
    modulusBits, leastIrreducibleCode]

/-- Multiply coordinate words using the supplied modulus bits, with zero padding or truncation
to its degree. A caller can reuse the same modulus across many products. -/
@[expose] def fieldMulMod (g a b : List Bool) : List Bool :=
  let word (x : List Bool) := List.ofFn fun i : Fin (g.length - 1) => x.getD i false
  modMulBits g (word a) (word b)

/-- The product always has the supplied modulus's coordinate width. -/
@[simp] theorem length_fieldMulMod (g a b : List Bool) :
    (fieldMulMod g a b).length = g.length - 1 := by
  exact length_modMulBits _ _ _ (by simp)

private theorem mk_polyOfBits_word {w : ℕ} (hw : w ≠ 0) (a : List Bool) :
    AdjoinRoot.mk (leastIrreducible w)
        (polyOfBits (List.ofFn fun i : Fin w => a.getD i false)) =
      fieldOfBits (basis hw) a := by
  rw [← AdjoinRoot.aeval_eq, aeval_polyOfBits, List.length_ofFn, Finset.sum_range,
    fieldOfBits, ofBits]
  exact Finset.sum_congr rfl fun i _ => by
    rw [basis_apply, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

/-- The table-free algorithm computes multiplication in the same power basis as
`fieldMul (fieldTable w)`. -/
theorem fieldOfBits_fieldMulMod {w : ℕ} (hw : w ≠ 0) (a b : List Bool) :
    fieldOfBits (basis hw) (fieldMulMod (modulusBits w) a b) =
      fieldOfBits (basis hw) a * fieldOfBits (basis hw) b := by
  obtain ⟨l, hl, hlen⟩ := exists_modulusBits_eq hw
  let word (x : List Bool) := List.ofFn fun i : Fin w => x.getD i false
  obtain ⟨-, hmlen, hprod⟩ := modMulBits_spec l (word a) (word b) (by simp [word, hlen])
  have hword : word (modMulBits (l ++ [true]) (word a) (word b)) =
      modMulBits (l ++ [true]) (word a) (word b) :=
    List.ofFn_getD_eq_of_length false (by simpa [hlen] using hmlen)
  have hp : polyOfBits (l ++ [true]) = leastIrreducible w := hl ▸ polyOfBits_modulusBits hw
  rw [hp, map_mul, mk_polyOfBits_word hw a, mk_polyOfBits_word hw b] at hprod
  rw [fieldMulMod, length_modulusBits hw, Nat.add_sub_cancel, ← mk_polyOfBits_word hw, hl]
  change AdjoinRoot.mk (leastIrreducible w) (polyOfBits (word _)) = _
  rw [hword, hprod]

end Cslib.BinaryField
